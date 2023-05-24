use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::Field, circuit::*, dev::MockProver, pasta::Fp, plonk::*, poly::Rotation,
};

#[derive(Debug, Clone)]
struct ACell<F: Field>(AssignedCell<F, F>);

#[derive(Debug, Clone)]
struct FiboConfig {
    pub advice: [Column<Advice>; 3],
    pub selector: Selector,
    pub instance: Column<Instance>,
}

struct FiboChip<F: Field> {
    config: FiboConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> FiboChip<F> {
    fn construct(config: FiboConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>, instance: Column<Instance>) -> FiboConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector = meta.selector();

        // enable the equality
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            vec![s * (a + b - c)]
        });

        FiboConfig {
            advice: [col_a, col_b, col_c],
            selector,
            instance
        }
    }

    fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
        a: Value<F>,
        b: Value<F>,
    ) -> Result<(ACell<F>, ACell<F>, ACell<F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0);
                let a_cell = region
                    .assign_advice(|| "a", self.config.advice[0], 0, || a)
                    .map(ACell)?;

                let b_cell = region
                    .assign_advice(|| "b", self.config.advice[1], 0, || b)
                    .map(ACell)?;

                let c_val = a.and_then(|a| b.map(|b| a + b));
                let c_cell = region
                    .assign_advice(|| "c", self.config.advice[2], 0, || c_val)
                    .map(ACell)?;
                Ok((a_cell, b_cell, c_cell))
            },
        )
    }

    fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        pre_b: &ACell<F>,
        pre_c: &ACell<F>,
    ) -> Result<ACell<F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                self.config.selector.enable(&mut region, 0);

                pre_b
                    .0
                    .copy_advice(|| "a", &mut region, self.config.advice[0], 0)?;

                pre_c
                    .0
                    .copy_advice(|| "b", &mut region, self.config.advice[1], 0)?; // what if offset not 0: NotEnoughRowsAvailable

                let c_val = pre_b
                    .0
                    .value()
                    .and_then(|b| pre_c.0.value().map(|c| *c + *b));

                let c_cell = region
                    .assign_advice(|| "c", self.config.advice[2], 0, || c_val)
                    .map(ACell)?;

                Ok(c_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &ACell<F>,
        row: usize
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.0.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F> {
    pub a: Value<F>,
    pub b: Value<F>,
}

impl<F: Field> Circuit<F> for MyCircuit<F> {
    type Config = FiboConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // we can define the instance here to share between chips
        let instance = meta.instance_column();
        FiboChip::configure(meta, instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FiboChip::construct(config);

        let (_, mut pre_b, mut pre_c) =
            chip.assign_first_row(layouter.namespace(|| "first row"), self.a, self.b)?;


        for _i in 3..10 {
            let c_cell = chip.assign_row(layouter.namespace(|| "next row"), &pre_b, &pre_c)?;
            pre_b = pre_c;
            pre_c = c_cell;
        }

        // SAME: assign_advice_from_instance
        chip.expose_public(layouter.namespace(
            || "out"), 
            &pre_c,
            2)?;

        Ok(())
    }
}
fn main() {
    let k = 4;
    let a = Fp::from(1);
    let b = Fp::from(1);
    let out = Fp::from(55);
    let circuit = MyCircuit {
        a: Value::known(a),
        b: Value::known(b),
    };

    let mut publics = vec![a, b, out];

    let prover = MockProver::run(k, &circuit, vec![publics.clone()]).unwrap();
    prover.assert_satisfied();

    // wrong out
    publics[2] += Fp::from(10);
    let _prover = MockProver::run(k, &circuit, vec![publics.clone()]).unwrap();
    // uncomment the following line will fail
    // _prover.assert_satisfied();
}

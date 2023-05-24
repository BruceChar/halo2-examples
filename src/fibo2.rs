use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::Field, circuit::*, dev::MockProver, pasta::Fp, plonk::*, poly::Rotation,
};

#[derive(Debug, Clone)]
struct FiboConfig {
    pub advice: Column<Advice>,
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
        let advice = meta.advice_column();
        let selector = meta.selector();

        // enable the equality
        meta.enable_equality(advice);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            let s = meta.query_selector(selector);
            let a = meta.query_advice(advice, Rotation::cur());
            let b = meta.query_advice(advice, Rotation::next());
            let c = meta.query_advice(advice, Rotation(2));
            vec![s * (a + b - c)]
        });

        FiboConfig {
            advice,
            selector,
            instance,
        }
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        rows: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "entire fibonacci table",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                self.config.selector.enable(&mut region, 1)?;

                let mut a_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    0,
                    self.config.advice,
                    0,
                )?;
                let mut b_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    1,
                    self.config.advice,
                    1,
                )?;

                for n in 2..rows {
                    if n < rows - 2 {
                        self.config.selector.enable(&mut region, n)?;
                    }
                    let c_val = a_cell.value().copied() + b_cell.value();

                    let c_cell = region.assign_advice(|| "c", self.config.advice, n, || c_val)?;
                    a_cell = b_cell;
                    b_cell = c_cell;
                }

                Ok(b_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit;

impl<F: Field> Circuit<F> for MyCircuit {
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

        let out_cell = chip.assign(layouter.namespace(|| "entire region"), 10)?;

        // SAME: assign_advice_from_instance
        chip.expose_public(layouter.namespace(|| "out"), &out_cell, 2)?;

        Ok(())
    }
}

fn main() {
    let k = 4;
    let a = Fp::from(1);
    let out = Fp::from(55);
    let circuit = MyCircuit;

    let mut publics = vec![a, a, out];

    let prover = MockProver::run(k, &circuit, vec![publics.clone()]).unwrap();
    prover.assert_satisfied();

    // wrong out
    publics[2] += Fp::from(10);
    let _prover = MockProver::run(k, &circuit, vec![publics.clone()]).unwrap();
    // uncomment the following line will fail
    // _prover.assert_satisfied();
}

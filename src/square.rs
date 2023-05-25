//! a^2 * b^2 = c

use halo2_proofs::{arithmetic::Field, circuit::*, plonk::*, poly::Rotation};
use std::marker::PhantomData;
type ResultNum<N> = Result<N, Error>;

trait NumericInstructions<F: Field>: Chip<F> {
    // a number
    type Num;

    // load a number into the circuit as a private input
    fn load_private(&self, layouter: impl Layouter<F>, a: Value<F>) -> ResultNum<Self::Num>;

    // load a number into the circuit as a fixed constant
    fn load_constant(&self, layouter: impl Layouter<F>, constant: F) -> ResultNum<Self::Num>;

    // return a * b
    fn mul(&self, layouter: impl Layouter<F>, a: Self::Num, b: Self::Num) -> ResultNum<Self::Num>;

    // expose a number as public input to the circuit
    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error>;
}

/// the chip to implement the instructions
/// chips store their own config, as well as type markers if necessary
struct FieldChip<F: Field> {
    config: FieldConfig,
    _marker: PhantomData<F>,
}

/// All chips need to implement Chip trait
impl<F: Field> Chip<F> for FieldChip<F> {
    type Config = FieldConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

/// chip state is stored in config. it's generated
/// by the chip during configuration, and then stored inside the chip
#[derive(Clone, Debug)]
struct FieldConfig {
    advice: [Column<Advice>; 2],

    /// public input column
    instance: Column<Instance>,

    /// to enable the multiplication gate
    s_mul: Selector,
}

impl<F: Field> FieldChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 2],
        instance: Column<Instance>,
        constant: Column<Fixed>,
    ) -> <Self as Chip<F>>::Config {
        meta.enable_equality(instance);
        meta.enable_constant(constant);
        // meta.enable_equality(constant); // Err: NotEnoughColumnsForConstants

        for column in &advice {
            meta.enable_equality(*column);
        }
        let s_mul = meta.selector();

        meta.create_gate("mul", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_mul = meta.query_selector(s_mul);

            vec![s_mul * (lhs * rhs - out)]
        });

        FieldConfig {
            advice,
            instance,
            s_mul,
        }
    }
}

#[derive(Clone)]
struct Number<F: Field>(AssignedCell<F, F>);

impl<F: Field> NumericInstructions<F> for FieldChip<F> {
    type Num = Number<F>;

    fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<F>,
    ) -> ResultNum<Self::Num> {
        let config = self.config();

        layouter.assign_region(
            || "load private",
            |mut region| {
                region
                    .assign_advice(|| "private", config.advice[0], 0, || value)
                    .map(Number)
            },
        )
    }

    fn load_constant(&self, mut layouter: impl Layouter<F>, constant: F) -> ResultNum<Self::Num> {
        let config = self.config();

        layouter.assign_region(
            || "load constant",
            |mut region| {
                region
                    .assign_advice_from_constant(|| "constant value", config.advice[0], 0, constant)
                    .map(Number)
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();

        layouter.constrain_instance(num.0.cell(), config.instance, row)
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> ResultNum<Self::Num> {
        let config = self.config();

        layouter.assign_region(
            || "mul",
            |mut region: Region<'_, F>| {
                config.s_mul.enable(&mut region, 0)?;
                a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                let value = a.0.value().copied() * b.0.value();
                region
                    .assign_advice(|| "lhs * rhs", config.advice[0], 1, || value)
                    .map(Number)
            },
        )
    }
}

#[derive(Default)]
struct MyCircuit<F: Field> {
    constant: F,
    a: Value<F>,
    b: Value<F>,
}

impl<F: Field> Circuit<F> for MyCircuit<F> {
    type Config = FieldConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column()];
        let instance = meta.instance_column();
        let constant = meta.fixed_column();
        FieldChip::configure(meta, advice, instance, constant)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let field_chip = FieldChip::<F>::construct(config);

        let a = field_chip.load_private(layouter.namespace(|| "load a"), self.a)?;
        let b = field_chip.load_private(layouter.namespace(|| "load b"), self.b)?;

        let constant =
            field_chip.load_constant(layouter.namespace(|| "load constant"), self.constant)?;

        let ab = field_chip.mul(layouter.namespace(|| "a * b"), a, b)?;
        let absq = field_chip.mul(layouter.namespace(|| "ab * ab"), ab.clone(), ab)?;
        let c = field_chip.mul(layouter.namespace(|| "constant * absq"), constant, absq)?;

        field_chip.expose_public(layouter.namespace(|| "expose c"), c, 0)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test() {
        use super::*;
        use halo2_proofs::{dev::MockProver, pasta::Fp};

        // the number of rows cannot exceed 2^k.
        let k = 8;

        // prepare the private and public inputs to the circuit
        let constant = Fp::from(17);
        let a = Fp::from(2);
        let b = Fp::from(3);

        let c = constant * a.square() * b.square();

        // initiate the circuit with the private inputs
        let circuit = MyCircuit {
            constant,
            a: Value::known(a),
            b: Value::known(b),
        };

        let dot_string = halo2_proofs::dev::circuit_dot_graph(&circuit);
        println!("{:?}", dot_string);
        // arrange the public input
        let mut public_inputs = vec![c];

        // given the correct public input
        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        // try some other public inputs
        public_inputs[0] += Fp::one();
        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        assert!(prover.verify().is_err());
    }
}

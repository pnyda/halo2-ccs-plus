use crate::query::Query;
use halo2_proofs::plonk::Expression;

#[derive(Debug, PartialEq)]
pub(crate) struct Monomial<F: ark_ff::PrimeField> {
    pub(crate) coefficient: F,
    pub(crate) variables: Vec<Query>,
}

// Convert a custom gate in Halo2, which is a polynomial, into a list of monomials.
// We need to first expand the polynomial in order to represent it in CCS.
// For example to constrain a column to be either 0 or 1 we ofter constrain (ColumnA - 1) * ColumnA = 0 in Halo2.
// We need to expand the custom gate into 2 monomials: 1 * ColumnA * ColumnA + (-1) * ColumnA = 0
pub(crate) fn get_monomials<
    HALO2: ff::PrimeField<Repr = [u8; 32]>,
    ARKWORKS: ark_ff::PrimeField,
>(
    expr: &Expression<HALO2>,
) -> Vec<Monomial<ARKWORKS>> {
    match expr {
        Expression::Constant(constant) => vec![Monomial {
            coefficient: ARKWORKS::from_le_bytes_mod_order(&constant.to_repr()),
            variables: vec![],
        }],
        Expression::Selector(query) => vec![Monomial {
            coefficient: 1.into(),
            variables: vec![Query::Selector(*query)],
        }],
        Expression::Advice(query) => vec![Monomial {
            coefficient: 1.into(),
            variables: vec![Query::Advice(*query)],
        }],
        Expression::Fixed(query) => vec![Monomial {
            coefficient: 1.into(),
            variables: vec![Query::Fixed(*query)],
        }],
        Expression::Instance(query) => vec![Monomial {
            coefficient: 1.into(),
            variables: vec![Query::Instance(*query)],
        }],
        Expression::Negated(expr) => get_monomials::<HALO2, ARKWORKS>(expr)
            .into_iter()
            .map(|original| Monomial {
                coefficient: original.coefficient.neg(),
                variables: original.variables,
            })
            .collect(),
        Expression::Scaled(expr, scalar) => get_monomials::<HALO2, ARKWORKS>(expr)
            .into_iter()
            .map(|original| Monomial {
                coefficient: original.coefficient
                    * ARKWORKS::from_le_bytes_mod_order(&scalar.to_repr()),
                variables: original.variables,
            })
            .collect(),
        Expression::Sum(lhs, rhs) => {
            let mut result = Vec::new();
            result.extend(get_monomials::<HALO2, ARKWORKS>(lhs));
            result.extend(get_monomials::<HALO2, ARKWORKS>(rhs));
            result
        }
        Expression::Product(lhs, rhs) => {
            let lhs_monomials = get_monomials::<HALO2, ARKWORKS>(lhs);
            let rhs_monomials = get_monomials::<HALO2, ARKWORKS>(rhs);
            let mut result = Vec::new();

            for lhs_monomial in lhs_monomials.iter() {
                for rhs_monomial in rhs_monomials.iter() {
                    let mut variables = Vec::new();
                    variables.extend(lhs_monomial.variables.iter().copied());
                    variables.extend(rhs_monomial.variables.iter().copied());

                    result.push(Monomial {
                        coefficient: lhs_monomial.coefficient * rhs_monomial.coefficient,
                        variables,
                    })
                }
            }

            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::Fq;
    use ff::Field;
    use halo2_proofs::pasta::Fp;
    use halo2_proofs::plonk::AdviceQuery;
    use halo2_proofs::poly::Rotation;

    // (ColumnA - 1) * ColumnA = 0
    // must be expanded into 2 monomials:
    // 1 * ColumnA * ColumnA + (-1) * ColumnA = 0
    #[test]
    fn test_get_monomials() {
        let subject: Expression<Fp> = Expression::Product(
            Box::new(Expression::Sum(
                Box::new(Expression::Advice(AdviceQuery {
                    index: 0,
                    column_index: 0,
                    rotation: Rotation(0),
                })),
                Box::new(Expression::Constant(Fp::ONE.neg())),
            )),
            Box::new(Expression::Advice(AdviceQuery {
                index: 1,
                column_index: 0,
                rotation: Rotation(0),
            })),
        );

        let result: Vec<Monomial<Fq>> = get_monomials(&subject);
        let must_be = vec![
            Monomial {
                coefficient: 1.into(),
                variables: vec![
                    Query::Advice(AdviceQuery {
                        index: 0,
                        column_index: 0,
                        rotation: Rotation(0),
                    }),
                    Query::Advice(AdviceQuery {
                        index: 1,
                        column_index: 0,
                        rotation: Rotation(0),
                    }),
                ],
            },
            Monomial {
                coefficient: (-1).into(),
                variables: vec![Query::Advice(AdviceQuery {
                    index: 0,
                    column_index: 0,
                    rotation: Rotation(0),
                })],
            },
        ];

        assert_eq!(result, must_be);
    }
}

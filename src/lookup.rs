use ark_ff::FftField;
use ark_ff::PrimeField;
use ark_ff::UniformRand;
use ark_poly::univariate::DensePolynomial;
use ark_poly::Polynomial;
use ark_poly::{EvaluationDomain, Evaluations, Radix2EvaluationDomain};
use ark_std::log2;
use ark_std::rand::rngs::OsRng;
use std::ops::Add;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Sub;

pub(crate) fn check_lookup_satisfiability<F: PrimeField>(subset: &[F], superset: &[F]) -> bool {
    let (subset_sorted, superset_sorted) = crate::lookup::sort(&subset, &superset);
    let is_multiset_equal =
        check_multiset_equality(&superset, &superset_sorted, &subset_sorted, &subset);
    let is_copying_this_or_that = copy_this_or_that(&superset_sorted, &subset_sorted);

    is_multiset_equal && is_copying_this_or_that
}

fn copy_this_or_that<F: PrimeField + FftField>(superset_sorted: &[F], subset_sorted: &[F]) -> bool {
    assert_eq!(subset_sorted.len(), superset_sorted.len());
    assert!(subset_sorted.len().is_power_of_two());
    let k = log2(subset_sorted.len());

    let original_domain = Radix2EvaluationDomain::new(1 << k).unwrap();
    // We need to expand the evaluation domain first, because we'll do polynomial multiplications later.
    // We'll need to handle polynomials with larger degrees.
    let expanded_domain = Radix2EvaluationDomain::new(1 << k << 1).unwrap();

    let mut subset_sorted = subset_sorted.to_vec();
    let A_prime = Evaluations::from_vec_and_domain(subset_sorted.clone(), original_domain)
        .interpolate()
        .evaluate_over_domain(expanded_domain);
    subset_sorted.rotate_right(1);
    let A_prime_shifted = Evaluations::from_vec_and_domain(subset_sorted, original_domain)
        .interpolate()
        .evaluate_over_domain(expanded_domain);
    let S_prime = Evaluations::from_vec_and_domain(superset_sorted.to_vec(), original_domain)
        .interpolate()
        .evaluate_over_domain(expanded_domain);

    let mut lagrange0: Vec<F> = vec![0.into(); expanded_domain.size()];
    lagrange0[0] = 1.into();
    let lagrange0 = Evaluations::from_vec_and_domain(lagrange0, expanded_domain);

    // (A'(X) - S'(X)) * (A'(X) - A'(X / omega)) = 0
    let constraint1 = A_prime.sub(&S_prime).mul(&A_prime.sub(&A_prime_shifted));
    // l_0(X) * (A'(X) - S'(X))
    let constraint2 = A_prime.sub(&S_prime).mul(&lagrange0);

    zero_test(&constraint1.interpolate(), original_domain)
        && zero_test(&constraint2.interpolate(), original_domain)
}

// a_prime must be multiset-equal to a.
// s_prime must be multiset-equal to s.
// We check 2 multiset equality at once.
fn check_multiset_equality<F: UniformRand + PrimeField + FftField>(
    superset: &[F],
    superset_sorted: &[F],
    subset_sorted: &[F],
    subset: &[F],
) -> bool {
    assert_eq!(subset.len(), superset_sorted.len());
    assert_eq!(subset.len(), subset_sorted.len());
    assert_eq!(subset.len(), superset.len());
    assert!(subset.len().is_power_of_two());
    let k = log2(subset.len());

    // Random challenges.
    // Maybe TODO: fiat shamir?
    let beta = F::rand(&mut OsRng);
    let gamma = F::rand(&mut OsRng);

    // Note that Z in Halo2 book is different from the witness vector Z in CCS
    // Z works as a proof of multiset equality
    let mut Z: Vec<F> = vec![1.into()];

    for i in 0..subset.len() {
        Z.push(Z.last().unwrap().clone());
        *Z.last_mut().unwrap() *= (subset[i] + beta) / (subset_sorted[i] + beta)
            * (superset[i] + gamma)
            / (superset_sorted[i] + gamma);
    }

    // We can safely unwrap here because Z will never have length 0.
    Z[0] = Z.pop().unwrap();
    // If A is indeed multiset-equal to A_prime, and S is indeed multiset-equal to S_prime,
    //   this operation does nothing, because the last element of Z is 1 anyway.
    // If one of the multiset equalities does not hold, the last element of Z will not be 1.
    //   and it will make the zero test we'll do next fail

    // ark_poly somehow doesn't support adding a constant to Evaluations so we need this
    let beta = Evaluations::from_vec_and_domain(
        // We'll later do polynomial multiplications so we need to expand the evaluation domain beforehand
        vec![beta; 1 << k << 2],
        Radix2EvaluationDomain::new(1 << k << 2).unwrap(),
    );
    let gamma = Evaluations::from_vec_and_domain(
        vec![gamma; 1 << k << 2],
        Radix2EvaluationDomain::new(1 << k << 2).unwrap(),
    );
    let one = Evaluations::from_vec_and_domain(
        vec![F::one(); 1 << k << 2],
        Radix2EvaluationDomain::new(1 << k << 2).unwrap(),
    );

    // A(X)
    let A = Evaluations::from_vec_and_domain(
        subset.to_vec(),
        Radix2EvaluationDomain::new(1 << k).unwrap(),
    )
    .interpolate()
    .evaluate_over_domain(Radix2EvaluationDomain::new(1 << k << 2).unwrap());
    // A'(X)
    let A_prime = Evaluations::from_vec_and_domain(
        subset_sorted.to_vec(),
        Radix2EvaluationDomain::new(1 << k).unwrap(),
    )
    .interpolate()
    .evaluate_over_domain(Radix2EvaluationDomain::new(1 << k << 2).unwrap());
    // S(X)
    let S = Evaluations::from_vec_and_domain(
        superset.to_vec(),
        Radix2EvaluationDomain::new(1 << k).unwrap(),
    )
    .interpolate()
    .evaluate_over_domain(Radix2EvaluationDomain::new(1 << k << 2).unwrap());
    // S'(X)
    let S_prime = Evaluations::from_vec_and_domain(
        superset_sorted.to_vec(),
        Radix2EvaluationDomain::new(1 << k).unwrap(),
    )
    .interpolate()
    .evaluate_over_domain(Radix2EvaluationDomain::new(1 << k << 2).unwrap());
    // Z(X)
    let Z_original =
        Evaluations::from_vec_and_domain(Z.clone(), Radix2EvaluationDomain::new(1 << k).unwrap())
            .interpolate()
            .evaluate_over_domain(Radix2EvaluationDomain::new(1 << k << 2).unwrap());
    Z.rotate_left(1);
    // Z(X * \omega)
    let Z_shifted =
        Evaluations::from_vec_and_domain(Z, Radix2EvaluationDomain::new(1 << k).unwrap())
            .interpolate()
            .evaluate_over_domain(Radix2EvaluationDomain::new(1 << k << 2).unwrap());

    // Somehow using + - * operators does not work!
    // I guess it's because Evaluations doesn't implement Copy
    let constraint1: Evaluations<F, Radix2EvaluationDomain<F>> = Z_shifted
        .mul(&A_prime.add(&beta))
        .mul(&S_prime.add(&gamma))
        .sub(&Z_original.mul(&A.add(&beta)).mul(&S.add(&gamma)));

    let mut lagrange0: Vec<F> = vec![0.into(); 1 << k << 2];
    lagrange0[0] = 1.into();
    let lagrange0 = Evaluations::from_vec_and_domain(
        lagrange0,
        Radix2EvaluationDomain::new(1 << k << 2).unwrap(),
    );
    let constraint2: Evaluations<F, Radix2EvaluationDomain<F>> =
        Z_original.sub(&one).mul(&lagrange0);

    zero_test(
        &constraint1.interpolate(),
        Radix2EvaluationDomain::new(1 << k).unwrap(),
    ) && zero_test(
        &constraint2.interpolate(),
        Radix2EvaluationDomain::new(1 << k).unwrap(),
    )
}

fn zero_test<F: FftField + PrimeField>(
    poly: &DensePolynomial<F>,
    domain: Radix2EvaluationDomain<F>,
) -> bool {
    let (q, _r) = poly.divide_by_vanishing_poly(domain);
    let random_challenge = F::rand(&mut OsRng);
    poly.evaluate(&random_challenge)
        == q.evaluate(&random_challenge) * domain.vanishing_polynomial().evaluate(&random_challenge)
}

// Given a multiset a = {2, 2, 1, 1} and a multiset s = {4, 2, 3, 1},
// Output a' = [1, 1, 2, 2] and s' = [1, 3, 2, 4]
// When a' changes at ith element, s'[i] == a'[i]
fn sort<F: PrimeField>(
    subset: &[F],
    superset: &[F],
) -> (
    Vec<F>, // subset sorted
    Vec<F>, // superset sorted
) {
    assert_eq!(subset.len(), superset.len());
    assert!(superset.len().is_power_of_two());

    let mut subset_sorted: Vec<F> = subset.to_vec();
    subset_sorted.sort();

    // TODO: Isn't there a better way to take intersection of 2 multisets?
    let mut superset_subset_intersection: Vec<F> = superset
        .iter()
        .copied()
        .filter(|elem| subset.contains(elem))
        .collect();
    superset_subset_intersection.sort();
    superset_subset_intersection.reverse();
    // We sort and reverse the array here because we'll later look at the smallest number in this array and sometimes pop the smallest number

    // TODO: Isn't there a better way to take difference of 2 multisets?
    let mut superset_subset_difference: Vec<F> = superset
        .iter()
        .copied()
        .filter(|elem| !subset.contains(elem))
        .collect();

    let superset_sorted: Vec<F> = subset_sorted
        .iter()
        .map(|a_i| {
            if superset_subset_intersection.last() == Some(a_i) {
                superset_subset_intersection.pop().unwrap()
            } else {
                superset_subset_difference.pop().unwrap()
            }
        })
        .collect();

    assert_eq!(superset_subset_intersection.len(), 0);
    assert_eq!(superset_subset_difference.len(), 0);

    (subset_sorted, superset_sorted)
}

#[cfg(test)]
mod tests {
    use ark_pallas::Fq;

    #[test]
    fn test_sort() {
        let subset: [Fq; 4] = [2.into(), 2.into(), 1.into(), 1.into()];
        let superset: [Fq; 4] = [4.into(), 2.into(), 1.into(), 2.into()];
        let (subset_sorted, superset_sorted) = super::sort(&subset, &superset);

        assert_eq!(subset_sorted, vec![1.into(), 1.into(), 2.into(), 2.into()]);
        assert_eq!(
            superset_sorted,
            vec![1.into(), 4.into(), 2.into(), 2.into()]
        );
    }

    #[test]
    fn test_multiset_equality_success() {
        let subset: [Fq; 4] = [2.into(), 2.into(), 1.into(), 1.into()];
        let superset: [Fq; 4] = [4.into(), 2.into(), 1.into(), 2.into()];
        let subset_sorted: [Fq; 4] = [1.into(), 1.into(), 2.into(), 2.into()];
        let superset_sorted: [Fq; 4] = [1.into(), 4.into(), 2.into(), 2.into()];

        assert!(super::check_multiset_equality(
            &superset,
            &superset_sorted,
            &subset_sorted,
            &subset
        ))
    }

    #[test]
    fn test_multiset_equality_fail() {
        let subset: [Fq; 4] = [1.into(), 2.into(), 1.into(), 1.into()];
        let subset_sorted: [Fq; 4] = [1.into(), 1.into(), 2.into(), 2.into()];
        let superset: [Fq; 4] = [4.into(), 2.into(), 1.into(), 2.into()];
        let superset_sorted: [Fq; 4] = [1.into(), 4.into(), 2.into(), 2.into()];

        assert!(!super::check_multiset_equality(
            &superset,
            &superset_sorted,
            &subset_sorted,
            &subset
        ))
    }

    #[test]
    fn test_copy_this_or_that_success() {
        let superset_sorted: [Fq; 4] = [0.into(), 1.into(), 2.into(), 3.into()];
        let subset_sorted: [Fq; 4] = [0.into(), 0.into(), 2.into(), 3.into()];

        assert!(super::copy_this_or_that(&superset_sorted, &subset_sorted))
    }

    #[test]
    fn test_copy_this_or_that_fail() {
        let superset_sorted: [Fq; 4] = [0.into(), 1.into(), 3.into(), 2.into()];
        let subset_sorted: [Fq; 4] = [0.into(), 0.into(), 2.into(), 3.into()];

        assert!(!super::copy_this_or_that(&superset_sorted, &subset_sorted))
    }
}

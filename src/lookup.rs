use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, Evaluations, Radix2EvaluationDomain};

fn check_lookup_satisfiability<F: PrimeField>(k: u32, subset: Vec<F>, superset: Vec<F>) -> bool {
    let (subset_sorted, superset_sorted) = crate::lookup::sort(k, &subset, &superset);

    let evaluation_domain = Radix2EvaluationDomain::new(1 << k).unwrap();
    // A(X), S(X), A'(X), S'(X) in the Halo2 book
    // https://zcash.github.io/halo2/design/proving-system/lookup.html
    let a = Evaluations::from_vec_and_domain(subset, evaluation_domain).interpolate();
    let s = Evaluations::from_vec_and_domain(superset, evaluation_domain).interpolate();
    let a_prime = Evaluations::from_vec_and_domain(subset_sorted, evaluation_domain).interpolate();
    let a_prime =
        Evaluations::from_vec_and_domain(superset_sorted, evaluation_domain).interpolate();

    false
}

// Given a multiset a = {2, 2, 1, 1} and a multiset s = {4, 2, 3, 1},
// Output a' = [1, 1, 2, 2] and s' = [1, 3, 2, 4]
// When a' changes at ith element, s'[i] == a'[i]
fn sort<F: PrimeField>(
    k: u32,
    subset: &[F],
    superset: &[F],
) -> (
    Vec<F>, // subset sorted
    Vec<F>, // superset sorted
) {
    assert_eq!(subset.len(), 1 << k);
    assert_eq!(superset.len(), 1 << k);

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
        let (subset_sorted, superset_sorted) = super::sort(2, &subset, &superset);

        assert_eq!(subset_sorted, vec![1.into(), 1.into(), 2.into(), 2.into()]);
        assert_eq!(
            superset_sorted,
            vec![1.into(), 4.into(), 2.into(), 2.into()]
        );
    }
}

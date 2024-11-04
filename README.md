# Roadmap for the development of the Rust implementation
## Learnings from the sage implementation
In my sage code, I implemented a PoC in the following steps.

1. Generate $M_j$ from the definition of custom gates, with no respect to copy constraints.
2. Apply copy constraints by deduplicating witnesses
3. Check if the CCS relation is satisfied.
4. Check if the lookup relation is satisfied.

Turns out this is not good because Step 4 has to know which element of Z represents which cell in the original table. The code to keep track of it during Step 2 was looking ugly. A better way to implement this would look like the below:

1. Generate a key-value map of `(column_index, row_index) -> z_index` from the copy constraints.
2. Generate $M_j$ from the above map and the custom gates.
3. Check if the CCS relation is satisfied.
4. Check if the lookup relation is satisfied.

This way Step 4 just has to read the key-value map generated in Step 1 to know which element of Z represents which cell in the original table. Thus it will be easier to check if a cell is in a lookup table.

## How do I hack the Halo2 internal?
We need to extract fixed columns, custom gates, copy constraints, and lookup constraints from the original Halo2 code. This can't be done within the configure phase as we don't know the values assigned in fixed columns until the synthesize phase is over. To run the synthesize phase, we need to call [`FloorPlanner::synthesize`](https://docs.rs/halo2_proofs/latest/halo2_proofs/plonk/trait.FloorPlanner.html#tymethod.synthesize). It expects a struct that implements [`Assignment`](https://docs.rs/halo2_proofs/latest/halo2_proofs/plonk/trait.Assignment.html).

So, to extract the necessary information from a Halo2 circuit, we need a custom implementation of `Assignment`. I have looked into existing implementations of `Assignment` such as [`MockProver`](https://docs.rs/halo2_proofs/latest/src/halo2_proofs/dev.rs.html#554) and [`Assembly`](https://docs.rs/halo2_proofs/latest/src/halo2_proofs/plonk/keygen.rs.html#48), but the both structs hold all the information we wanna read from our crate as private members only accessible from their crate. This necessitates a new implementation of `Assignment` that exposes all the information we need to our crate.

This sounds like a daunting task but in reality we can just copy-paste the code where `MockProver` implements `Assignment`, make it expose their internal state, and cut out the unnecessary lines.

## Roadmap
1. Implement the custom `Assignment`.
2. Make the transpiler generate a CCS instance from the custom gates, the copy constraints and the assigned fixed columns.
3. Make the transpiler generate the witness vector $Z$ from the assigned advice columns.
4. Make the transpiler generate a CCS+ instance, by incorporating lookup constraints. Halo2 supports constraining an expression instead of a cell to be in a lookup table, so we need to append expressions computed at each row at the end of $Z$.
5. Write tests and examples.

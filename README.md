A transpiler that transpiles a Halo2 circuit into a CCS+ circuit


# Recap: How does lookup in Halo2 work?
It's basically plookup but with slight modifications.
- https://youtu.be/uGjbczKGm4s?si=9aXzQomfHjSmzWrI


# Recap: How does lookup in CCS+ work?
[the CCS paper](https://eprint.iacr.org/2023/552.pdf) describes CCS+ in the appendix. CCS+ is basically CCS, but with an ability to constrain specific elements in $Z$ to be in table $T$. The CCS+ described in the paper is only applicable for the case where there is only **single** **static** lookup table. It seems easy to generalize this for the case where there are **multiple** lookup tables. But it's not clear to me how we can generalize this into supporting **dynamic** lookup tables, as PSE Halo2 does with [lookup_any](https://privacy-scaling-explorations.github.io/halo2/halo2_proofs/plonk/struct.ConstraintSystem.html#method.lookup_any).

# Roadmap
For the reasons I described earlier, I will develop this transpiler to support Zcash Halo2, not PSE Halo2. Zcash Halo2 supports only static lookup tables. This is similar to CCS+. Thus it must be far easier to write a Zcash -> CCS+ transpiler, compared to PSE Halo2 -> CCS+ transpiler.
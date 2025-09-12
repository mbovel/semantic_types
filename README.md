# Semantic Types Experiments

- [`systemf_erased.v`](systemf_erased.v): soundness proof of erased System F in Rocq, using a definitional interpreter, Autosubst and semantic types.

## References

- [Type Soundness Proofs with Definitional Interpreters](https://doi.org/10.1145/3093333.3009866)  
  Nada Amin and Tiark Rompf, POPL 2017
  
- [Autosubst: Reasoning with de Bruijn Terms and Parallel Substitutions](https://doi.org/10.1007/978-3-319-22102-1_24)  
  Steven Schäfer, Tobias Tebbi and Gert Smolka, ITP 2015
  
- [A Logical Approach to Type Soundness](https://doi.org/10.1145/3676954)  
  Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal, Journal of the ACM 2024

## Building

```bash
# Compile Coq proof
make compile

# Extract and run OCaml evaluator
make run
```

The extracted OCaml evaluator demonstrates the definitional interpreter running on System F terms.

# Motivic incremental validated checkpoint: 165 sources

This checkpoint adds 15 fully batch-validated Lean files to main `581293ea17843e6028d1a87aa055e55d918f9698`, whose complete CI passed at https://github.com/kangxyz/colib/actions/runs/42774908636 . All existing source bytes and published Library IDs are preserved. The root adds exactly nine production imports.

## New results

- Relative sheaf cohomology: the actual short exact free-sheaf presentation, six-term Ext sequence, signed connecting map and three lifting statements, naturality for squares and coefficients, and refinement zero-detection. Four production owners and an actual consumer comprise five files and 50 native declarations.
- Generic points and lengths: actual geometric generic-point transport, flat generic-stalk length, and their full exterior-incidence specializations, without replacing the incidence by its reduction. Four producer/consumer pairs comprise eight files and 43 native declarations.
- Finite pushforward and flat pullback: the actual finite cycle comparison and push-pull formula with residue degrees. A producer/consumer pair comprises two files and four native declarations. The proof discharges the existing finite/affine hypotheses directly and avoids importing an unrelated broad proper-coherence closure.

Each new producer and actual consumer compiled. Every new production owner passed all 15 native declaration linters and ordinary-axiom closure; exact source textstyle also passed. Source and output hashes were checked again for this checkpoint. This is scoped incremental acceptance of 97 new declarations, not a fresh aggregate native 165-source build. CI is intentionally skipped on this checkpoint. No kernel replay was run.

The 165-file contribution now contains 91 production files and 74 actual consumers. This count is not the size of the whole repository or a completion percentage. General signed exterior composition and its remaining Tor/Koszul comparisons are still being validated. Later transfer singular, signed-shift and motivic-complex drafts are excluded. No weight-one quasi-isomorphism or strict A1-invariance endpoint is claimed by this checkpoint.

All work retains Lean 4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 and Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7. The earlier 150-source historical checkpoint report is unchanged. `motivic-20261110-next-source-manifest.json` records the exact 165 source hashes.

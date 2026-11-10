# Performance

For slow CI, compare named step durations before changing compiler limits. Record
compiler, manifest, workflow source and whether the run reused a compatible cache.
Separate production compilation, acquisition, hashing/packing, transfer and checks.
A new cache schema's first run is not a steady-state measurement. Code changes also
prevent treating whole-run differences as a controlled compiler benchmark.

Colib's ordinary dependencies are supplied by Mathlib's official cache. Do not
repack the entire Mathlib build into a project dependency or tools checkpoint.
Exclude official Mathlib production outputs from project checkpoints, retain small
checker outputs, preserve the independent Stacks boundary,
and retain native input verification and axiom/lint predicates.

The [CI checkpoint case](performance/ci-mathlib-checkpoint.md) records the regression,
original measurements, exact runs, and the compact-path validation. Its
[step timings](performance/ci-timings.json) preserve the complete measured phases.

When an elaboration timeout is attributed to a nested `obtain` in a large
proposition, profile the command and try `Exists.elim` with explicit conjunction
projections at the same heartbeat budget. See the
[finite mixed generation case](performance/finite-mixed-exists-elim.md).

If profiling points to `CoeT` while elaborating an equality of K-group
homomorphisms, provide the equality's native homomorphism type explicitly.
See the [fine K-product case](performance/fine-k-product-equality-type.md).

When an expanded consumer independently infers the correct production proof
and the final elaborator conversion is costly, reuse that exact local proof
term at the goal. Keep the fully stated equality and verify the resulting
declaration with the ordinary native build. The
[Milnor branch consumer case](performance/milnor-branch-consumer-conversion.md)
records the applicable boundaries and measurements.

In an instance-heavy DVR argument, isolate the ramification witnesses and
map injectivity in small typed proofs. For a branch sum, compose the actual
additive maps before applying the finite-sum theorem once. Use pointwise
equality transport for the literal branch coordinates. The
[complete DVR case](performance/complete-dvr-instance-and-sum-elaboration.md)
records the diagnosed phases and native validation.

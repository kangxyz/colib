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

When `colimit.pre` asks the elaborator to identify colimits of two separately
expressed diagrams, build the cocone on the actual source diagram and apply
`colimit.desc`. Check the map on each original colimit injection. The
[coniveau stage case](performance/coniveau-stage-colimit-conversion.md)
records the failed conversion and the native check of the pointwise cocone.

When the consumer needs distinguishedness after an isomorphism of the
middle term, transport the property in a generic pretriangulated category.
Give the specialization the typed equations of the original arrows. The
[middle quotient case](performance/coniveau-stage-colimit-conversion.md#distinguishedness-after-a-middle-quotient-comparison)
records the native kernel timeout and the checked transport.

For an isomorphism proved through a functor factorization, state the two
functors' equality at its native type and transport `IsIso` in a generic
lemma. The [open-pair case](performance/coniveau-stage-colimit-conversion.md#functor-transport-in-open-pair-excision)
records the transport of both the literal relative quotient map and shifted Hom.

When a whiskered restriction lands in a differently associated diagram,
build the comparisons using functor associators. Check their identity
components on the original representatives before applying the colimit
maps. The [ambient restriction case](performance/coniveau-stage-colimit-conversion.md#associating-ambient-restriction-diagrams)
records the typed transport for whole support stages and adjacent windows.

For the point-to-window map, construct the inverse-excision maps and
their naturality before defining the cocone on the actual neighbourhood
diagram. Apply `colimit.desc` to that named cocone. The
[point window case](performance/coniveau-stage-colimit-conversion.md#colimit-descent-for-the-point-to-window-map)
records the successful separation of these declarations.

For a spectral object of opposite triangles, supply the original typed
boundary, naturality, and distinguishedness of the normalized positive
triangle. Assemble the opposite triangles in the abstract category.
The [closed-support case](performance/coniveau-stage-colimit-conversion.md#opposite-triangles-in-the-closed-support-spectral-object)
records the successful split and checks the represented boundary.

If `checkType` times out on a private naturality statement after
production compilation succeeds, inspect the stored statement under
the linter's default reducibility. Pass the concrete equality to the
existing generic consumer or package the components as a natural
isomorphism. The [naturality lint case](performance/coniveau-stage-colimit-conversion.md#naturality-statements-in-declaration-lint)
records the three coniveau examples with their original maps.

When a finite cover jointly detects represented cohomology classes,
prove separation on a generic coproduct cofan and supply the
original comparison to represented Hom at the specialization. The
[window generation case](performance/coniveau-stage-colimit-conversion.md#finite-generation-by-the-point-groups)
records the separate geometric, additive and cofan arguments.

If a declaration using a section variable reports a synthetic placeholder
or an unknown identifier, check the variable's stored type. Spell out
parameters hidden in local notation in the `variable` command. The
[section notation case](performance/section-variable-notation.md) records
the pinned reproducer and the corresponding checks for ordinary Zariski
opens and a normal-bundle Thom chart.

When composing cohomology comparisons on large sites, first check
the composition on an ordinary coefficient and an abstract isomorphism
of presheaves. The [ordinary opens specialization](performance/section-variable-notation.md#specializing-the-cohomology-comparison)
records the accepted composition and its bounded specialization.

When a branch proof combines the construction of a quotient-field
equivalence with transport of nested norms, prove the two commuting field
squares first. Compare the norms in a separate typed lemma that takes these
squares as inputs, and apply it to the literal polynomial factor. The
[pure prime compositum case](performance/milnor-branch-consumer-conversion.md#pure-prime-compositum)
records the native kernel timeout and the checked split.

In an instance-heavy DVR argument, isolate the ramification witnesses and
map injectivity in small typed proofs. For a branch sum, compose the actual
additive maps before applying the finite-sum theorem once. Use pointwise
equality transport for the literal branch coordinates. The
[complete DVR case](performance/complete-dvr-instance-and-sum-elaboration.md)
records the diagnosed phases and native validation.

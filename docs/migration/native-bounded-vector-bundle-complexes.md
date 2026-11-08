# Native bounded vector-bundle complexes

## Chosen objects and faithful source correspondence

COL-0313 uses the existing Stacks property
`Stacks.Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex` on the actual
`CochainComplex X.Modules ℤ`. Its definition is native `CochainComplex.plus` and
`CochainComplex.minus`, together with native finite local freeness in every degree. The
compiled term-bound equivalence identifies these bounds with global vanishing of the terms
outside an integer interval. It does not substitute bounded cohomology.

This is the mathematical predicate in
`Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Strict.lean` at
`2c34f185fa859e862661f939cd216b07bcccfb26`, used by Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The audited original Strict source has Git blob
`69091ab6f4866a97717ab2e0c30a31249a72c4bf` and SHA-256
`4cfd15796c6de0759e0b370e62b81d300153082084c7a0f0986eb04e6fd08525`.
The actual native category of vector bundles is `Scheme.Vect`; no earlier Aglib category,
property alias or compatibility layer is reintroduced.

The different native property `StrictlyPerfect.IsStrictlyPerfect`, defined in
`StacksFrontier/Topology/Sheaves/Cohomology/StrictlyPerfect/FiniteFreeSummands.lean`, asks that
all terms be retracts of globally finite free sheaves. This is not the definition used here.
In particular a finite locally free sheaf need not be a global finite-free retract. Native
Stacks already supplies the faithful bounded locally free property as well as this stronger
property; their similar terminology is not evidence that they are equal.

## Actual closure and inclusions

- `BoundedFiniteLocallyFree` proves actual zero, chain-isomorphism and short-exact extension
  closure on every scheme. Extension closure invokes the native locally split extension
  theorem for finite locally free sheaves. The global bounds are preserved separately.
- Every integer shift and every one-degree complex retain the native property. The original
  vector bundle is placed in degree zero, without choosing a replacement complex.
- `BoundedFiniteLocallyFreePerfect` uses the actual rotated mapping-cone short exact sequence
  for cone closure. Native Stacks Tag 0F8I gives perfectness of the original bounded complex.
  Its actual derived representative is related by the native quotient/Qh isomorphism.
- `BoundedFiniteLocallyFreeWaldhausen` inherits the exact structure on the full chain category.
  Cofibrations are monomorphisms whose actual quotient remains bounded finite locally free;
  they are not silently enlarged to all ambient monomorphisms. Weak maps are the original
  homology-based quasi-isomorphisms. The literal inclusion into the existing ambient-mono
  perfect-complex structure is exact.
- `VectorBundleComplexInclusion` proves exactness of the actual single-complex functor,
  including all short exact sequences of vector bundles and their actual cofibration
  pushouts. No global splitting of those sequences is assumed.
- `BoundedFiniteLocallyFreeJoint` and `BoundedFiniteLocallyFreeOpposite` use the established
  generic signed cylinder and degree-reversing opposite-complex machinery. Their actual
  second-endpoint section, opposite inclusion, common-cylinder comparison, and all three
  inverse endpoint/projection equations retain the original maps. The dual cofibrations
  are admissible epimorphisms, not a claim that every epimorphism is admissible.
- `AlgebraicGeometry/KTheory/BoundedFiniteLocallyFree` gives the connective S-construction
  K-groups and canonical normalized vector-bundle and strict-to-perfect K-maps. It does not
  assert either map is an equivalence.

## Original Quillen endpoints

The global term bounds and extension theorem are at lines 44–50 and 79–100 of the pinned
Aglib Strict source above. Tag 01C6 supplies the finite locally free definition, while native
`FiniteLocallyFree.Extension` supplies the extension theorem. Tag 0F8I supplies the perfectness
input, not the Waldhausen exactness assertion.

The direct Quillen source crosswalk is to `PerfectComplexes/Strict.lean:33-40`,
`VectorBundleInclusion.lean:36-66`, `KTheory.lean:61-65`,
`StrictJointData.lean:33-46`, and the strict part of `OppositeJointData.lean:40-100` in
`Quillen/AlgebraicGeometry`, at the exact Quillen revision above. The new actual native
perfect target is constructed using native Stacks perfectness rather than importing or
postulating the earlier local-perfect predicate. Generic exact-category, Waldhausen and
opposite-cylinder results remain at their existing lower owners.

## Scope and validation boundaries

No affine, Noetherian, quasi-compactness, resolution-property or global projectivity
hypothesis is added to these foundations. The global finite-free-retract predicate is never
substituted for finite local freeness, and local perfectness on an arbitrary scheme is not
replaced by a global uniform Tor-amplitude convention.

COL-0313 does not prove Q/S comparison, Gillet-Waldhausen, geometric derived-image
approximation, strict-to-perfect K-equivalence, fine open localization or nonconnective
localization. In this integrated topic, COL-0314 separately proves actual relative-image
approximation conditional on HasDerivedRoofs. The geometric roof and complement/density
theorems remain open.

Author source correspondence, local Lean compilation, independent mathematical review and
remote lint/axiom/Library validation are distinct evidence. The handoff records exact sources,
selected native dependencies, all five artifact families and actual producer receipts. The
shared root import and chapter/migration edits were proposals at component freeze.
The integrated native-perfect-foundations topic now includes those registrations.

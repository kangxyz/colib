# Literal perfect pullback compatibility

## Exact source and mathematical scope

Original Quillen revision: `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

- `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Functor.lean:101-106`:
  the square between actual flat pullback and the literal bounded-flat inclusion.
- `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullback.lean:77-88`:
  equality of arbitrary perfect K-pullback with the original exact flat and open maps.
- `Quillen/AlgebraicGeometry/PerfectComplexes/FlatPullback.lean:68-91`:
  the old map is the canonical KMap of genuine flat pullback; open comparison uses
  an actual natural isomorphism of chain functors.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/FlatPullback.lean:135-139`:
  geometric restriction-pullback comparison. Its native counterpart is the existing
  `perfectRestrictIsoFlatPullback`, built from Mathlib's `restrictFunctorIsoPullback`.
- `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullbackFunctor.lean:29-62`:
  group-valued functor and literal natural comparison, consumed from COL-0326.
- `Quillen/AlgebraicGeometry/PerfectComplexes/PairPullback.lean` handles supported and
  relative-open pullbacks. It is inspected context, not a claimed migration in this item.

## Same maps, not replacement equivalences

The native all-perfect category is the existing full subcategory of native Stacks perfect
complexes. The bounded-above flat model retains its original chain objects and maps. Its
inclusion followed by flat pullback and its pullback followed by inclusion are definitionally
the same chain functor; `boundedAboveFlatPerfectInclusionFlatPullbackIso` is `Iso.refl`.
Canonical KMap composition and isomorphism invariance prove the actual inclusion square.
The already-proved bijectivity of the unchanged inclusion KMap then uniquely identifies
`perfectKPullback` with the canonical KMap of `perfectFlatPullback_waldhausenExact`.
No desired naturality equation or comparison equivalence is an extra hypothesis.

For open immersions, the actual geometric chain NatIso compares the same flat map with
ordinary restriction. The older open-subset functor is also identified on actual chains,
so the endpoint is exactly `perfectComplexesRestrictKMap`, not a newly chosen substitute.
`perfectOpenKRestrict` alone has a relative coarse source. Only its existing composite
with `perfectOpenKMap` has ambient perfect K-theory as source, and that precise composite
is identified with `perfectKPullback`.

## Hypotheses and degrees

For `f : X → Y`, equality with the old flat map requires `[Flat f]` and only
`CompactSpace Y`. Open immersion equality and open-subset equality require only target
compactness; the open need not be compact. No quasi-separatedness, regularity, resolution
property, or source compactness is added.

Composition with an exact flat left factor needs only compactness of the final target.
For a commuting square `j ≫ f = g ≫ k`, with open immersions `j : U → X` and `k : V → Y`,
the ambient restriction square needs compactness of `Y` and `V`, precisely the targets
where arbitrary perfect pullback uses the inverse comparison. Neither `U` nor `X` needs
compactness. The results hold for every `n : ℕ`, including zero.

The consumer spells out full signatures, including the exact KMaps, literal chain NatIso,
identity, composition, the coarse composite, commuting open squares, and degree zero.

## Boundary

These are equalities of actual canonical group maps. They do not assert whole-prespectrum
homotopy, a supported/relative pullback construction, global localization, arbitrary scalar
descent, TT geometry, or Bass results. No Aglib import or compatibility wrapper is introduced.

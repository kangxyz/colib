# Prescribed cofiber-prism boundary: COL-0297

This single milestone retains the data-valued cofiber boundary, its exact reversed
canonical-fiber prefix and its degree-one normalization. It adapts the selected
original constructions at Quillen commit
[`c561118b7795eb9780be9ed391c3251d6a4d0afd`](https://github.com/kangxyz/quillen-k-theory/tree/c561118b7795eb9780be9ed391c3251d6a4d0afd).
The source cuts and native owners below delimit the contribution.

## Actual prism and boundary

Let `{C : Type u} [Category.{v} C] [HasZeroMorphisms C]`, `W : Structure C`,
`i : A ⟶ B`, `q : B ⟶ Q`, `hi : W.cof i`, `hwi : W.weq i`, and
`hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)`.
The displayed quotient is retained literally. Its zero-to-quotient arrow is weak
by the actual gluing axiom, not an additional acyclicity assumption.

Write `a,b,c` for the actual object loops of `A,B,Q`, and `e` for the constant
based loop. The continuous cube `C(r,s,t)` has independent **comparison r,
nerve s and object-loop t**, in that order. Its curried square is
`F(r,s)(t) = C(r,s,t)`.

- The whole nerve face `s=0` is the identity-cofiber triangle `(1_A, A → W.zero)`;
  `s=1` is the displayed triangle `(i,q)`.
- The whole comparison face `r=1` is the original weak square of `i`.
  At `r=0`, the source identity square is concatenated with the actual weak
  zero-to-quotient square in **loop time t**.
- `t=0` and `t=1` are the actual basepoint for both moving parameters independently.
- The S-faces `δ₂,δ₁,δ₀` are respectively source identity, inclusion and
  zero-to-quotient, as equalities of entire grid functors including mixed maps.

Realization uses the actual inverse product-simplex comparison. The cofiber
triangle is the specified affine standard-simplex homotopy mapped through its
characteristic map, with its original casts. No diagonal restriction or selected
`Homotopic` witness replaces these families.

The four paths in the original based-loop space are

- `P = cofiberPrismPrefixLoopPath : Path (a.trans e) (a.trans c)`,
  with `P(s)(t) = C(0,s,t)`;
- `H = cofiberObjectLoopPath : Path (a.trans c) b`;
- `E = identityCofiberSuffixPath A : Path (a.trans e) a`;
- `I = weakObjectSquareLoopPath i hwi : Path a b`.

The endpoint is the actual data
`cofiberBoundaryTrack : (P.trans H).Homotopy (E.trans I)`.
Its values are literally `cofiberPrismBoundaryHomotopy`, namely `F` composed
with native `squareBoundaryPathHomotopy`. The square routes are `(0,s)` then
`(r,1)`, versus `(r,0)` then `(1,s)`. Their comparison is the specified
coordinatewise affine interpolation; its parameter is independent of boundary
time and object-loop time. Every comparison fixes start `a.trans e` and end `b`.

Boundary concatenation splits **boundary time s** at `s ≤ 1/2`, with the original
`2*s` and `2*s-1` branches. Comparison-zero prefix concatenation instead splits
**loop time t** at `t ≤ 1/2`, with `2*t` and `2*t-1`. The full application and
route laws retain the corresponding interval witnesses.

## Exact reversed canonical-fiber prefix

For `V : Structure C` and `N : NestedWeakEquivalences V`, take `W=N.coarse`.
Let `XQ = cofiberPrismAcyclicQuotient N i q hi hwi hQ`. Its underlying object is
literally `Q`, certified acyclic by gluing. The stored canonical-fiber coordinate is

`(canonicalFiberObjectLoop N XQ t).val.2 s = weakSquare(0→Q)(1-s,t)`.

This comes from the actual transformation-cylinder/square identity, including
mixed maps and strict chosen-zero equations. It is not inferred from endpoint
agreement. The complete quotient face obeys

`cofiberPrismRealization (face δ₀(t),1-s) =
  (canonicalFiberObjectLoop N XQ t).val.2 s`.

The existing loop/fiber homeomorphism transposes the two coordinates without
another reversal. With `L_a δ = a.trans δ`, the exact prefix law is

`L_a ((canonicalFiberObjectLoopTranspose N XQ).val.2 s) t = C(0,1-s,t)`.

Combining this general production theorem with COL-0296's unchanged actual-point
formulas gives equality of the **entire stored continuous paths**:

- `(canonicalFiberObjectPrefixed N A XQ).val.2 = P.symm.toContinuousMap`;
- `(canonicalFiberObjectPrefixTransport N A XQ).val.2 =
  (P.symm.trans E).toContinuousMap`;
- the same latter path is stored by `canonicalFiberComponentEquiv N A` applied
  to `canonicalFiberObjectLoopTranspose N XQ`.

The endpoint regression leaf states these whole-path identities explicitly using
extensionality, the general prefix theorem and the existing transport law.
The fine source remains the literal fine `A`-loop followed by the fine `Q`-loop.
These are actual fibers of
`basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)`.
No weakness of the canonical comparison or fibration theorem is assumed.

## Degree-one normalization and its limit

`identityCofiberComponentEquiv A n` is left-prefix equivalence followed by
`pathTransport E n`, for every `n`. The normalization assertions are specifically

`pathTransport E 1 x = pathTransport (loopRightUnitPath a) 1 x`

for every `x : HomotopyGroup.Pi 1 (Path W.kBasepoint W.kBasepoint) (a.trans e)`, and

`identityCofiberComponentEquiv A 1 = loopLeftComponentHomotopyEquiv a 1`.

Their proofs use component-equivalence surjectivity and path-transport naturality.
They compare induced maps in degree one. They do not identify `E` with the
right-unit path as paths or continuous families, and do not assert normalization
in every degree merely because the constructor exists in every degree.

Independent category universes `u,v` and realization universe `max u v` are
retained. Weak-square and bisimplex primitives need no zero-morphism instance;
cofiber geometry and the identity suffix retain it. `oneDiagram_transformation_app`
keeps four category universes. The subsequent original transformation statements
keep their common source/target universe bounds and explicit strict chosen-zero
equalities. No `SmallCategory`, saturation, extension, factorization, cylinder,
connectivity, fibration or canonical-comparison weakness hypothesis is added.

## Exact source cuts and native ownership

There are **27 new production leaves, 84 new declarations and five unchanged
moved native definitions**, plus exactly four existing-file source overrides.
The native namespaces remain `CategoryTheory.Waldhausen` and its original
`Structure`, `QuotientRows` and `Fibration` subnamespaces.

In the tables, original paths start at `Quillen/Waldhausen/` at the pinned commit.
Every abbreviated path ends in `.lean`. `CT` means
`Colib/CategoryTheory/Waldhausen/`; `KT` means `Colib/KTheory/Waldhausen/`;
`GC` means `GrothendieckComparison/`; `SC` means `SConstruction/`; and `F` means
`Fibration/`. A range identifies complete selected declarations, not a new claim
about excluded declarations elsewhere in the original file.

### Categorical owners: 11 new leaves, 24 new declarations and five moves

| Native owner | Original source and exact selection |
| --- | --- |
| `CT/Rows/CofiberTwoComparison` | `SC/Rows/CofiberTwoComparison:28-91,101-125`: quotient weakness, object equality, component, natural transformation, row comparison and row weakness |
| `CT/Rows/CofiberTwoPrism` | `SC/Rows/CofiberTwoPrism:30-55`: all five declarations |
| `CT/Rows/CofiberPrismFaces` | `GC/CofiberPrismFaces:31-144`: only the three whole-functor S-face equalities |
| `CT/Rows/NerveReindex` | `SC/Rows/NerveReindex:22-31`: the one nerve-reindex theorem |
| `CT/Rows/OneRowTransformation` | `SC/Rows/OneRowTransformation:30-38`: only `oneDiagram_transformation_app` |
| `CT/Rows/WeakObjectSimplex` | Frozen native `KT/GC/WeakRelations:40-48`: byte-identical `oneWeakArrow` and `weakObjectSimplex`, including their docstrings |
| `CT/SC/ObjectSimplex` | Frozen native `KT/GC/ObjectLoops:36-54`: byte-identical `intervalProjection`, `rowSimplex` and `kZeroObjectSimplex`, including their docstrings |
| `CT/SC/BisimplexFamily` | `SC/BisimplexRealization:27-38`: only the two simplicial family declarations |
| `CT/SC/WeakObjectCylinder` | `GC/WeakObjectCylinder:29-58`: `weakObjectSimplex_cylinder` |
| `CT/SC/ObjectTransformationSquare` | `SC/ObjectTransformationSquare:37-58`: the whole categorical cylinder equality |
| `CT/SC/WeakObjectCompositionPrism` | `GC/WeakObjectCompositionPrism:39-55`: grid, certificate and first face; `GC/WeakObjectCompositionBased:24-45`: whole constant-vertex family theorem |

The five definitions move from the frozen native source at `20c70502` without
aliases, adapters, renaming or duplicated declaration sites. `ObjectLoops` and
`WeakRelations` import the new lower owners and otherwise retain their existing
content after the exact extractions. The third override removes **only** the
unused `public import Colib.KTheory.Waldhausen.Map` line from
`CT/Rows/PointwisePushouts`; its four theorem bodies and every other byte remain.
This removes the old inverse dependency through `OneRow`. The fourth override adds
only the direct `public import Colib.KTheory.Waldhausen.Basic` to
`KT/Cofinality/GradedKZero`, which uses that owner and must not depend on the
removed inverse chain. Its mathematical bodies are unchanged. Source-level import
inspection gives all new CT leaves purely categorical closures; native compilation
must validate the retained imports. No existing COL-0296 binding is changed.

### Continuous owners: nine leaves, 42 new declarations

| Native owner | Original source and exact selection |
| --- | --- |
| `KT/BisimplexRealization` | `SC/BisimplexRealization:41-81`: all four continuous declarations |
| `KT/ObjectTransformationTrack` | `SC/ObjectTransformationTrack:34-67`: both declarations |
| `KT/ObjectTransformationSquareRealization` | `SC/ObjectTransformationSquareRealization:34-75`: the full inverse-product/cylinder comparison |
| `KT/GC/CofiberPrismRealization` | `GC/CofiberPrismRealization:31-108`: all five declarations |
| `KT/GC/CofiberPrismHomotopy` | `GC/CofiberPrismHomotopy:32-140`: all six declarations |
| `KT/GC/CofiberPrismComposition` | `GC/CofiberPrismComposition:32-154`: all ten declarations |
| `KT/GC/WeakObjectIdentitySquare` | `GC/WeakObjectIdentitySquare:24-76`: both declarations |
| `KT/GC/WeakObjectCompositionRealization` | `GC/WeakObjectCompositionPrism:78-107`: three realization declarations; `GC/WeakObjectCompositionBased:48-75`: entire realized constant-vertex triangle |
| `KT/GC/WeakObjectSquareTrack` | `GC/WeakObjectSquareTrack:31-134`: all seven square declarations; `GC/WeakObjectCompositionTrack:29-35`: only `weakObjectSquareLoopPath` |

The selected composition fragment constructs its first edge by nerve reindexing
and its entire vertex triangle by a constant-functor equality and realization.
It assumes no `weakObjectCompositionCube`. No full weak-composition cube, based
or track facade is imported. The original comparison-weak proof ends at line
125, the selected prism faces at line 144, and the realized Based fragment at
line 75; all final proof lines are included.

### Boundary/fiber owners: seven leaves, 18 new declarations

| Native owner | Original source and exact selection |
| --- | --- |
| `KT/F/CanonicalFiberObjectSquare` | `F/CanonicalFiberObjectLoop:63-76`: only the acyclic transformation and reversed-coordinate law; `F/CanonicalFiberObjectSquare:30-47`: whole component-square law |
| `KT/F/CofiberPrismFiber` | `F/CofiberPrismFiber:33-70`: all three declarations |
| `KT/F/CofiberPrismLeftPrefix` | `F/CofiberPrismLeftPrefix:56-65`: only `cofiberPrismCompositionCube_zero_leftPrefix` |
| `KT/F/CofiberPrismBoundary` | `F/CofiberPrismBoundary:35-99`: all four declarations |
| `KT/F/CofiberBoundaryTrack` | `F/CofiberBoundaryTrack:31-109`: all four declarations |
| `KT/F/IdentityCofiberComponent` | `F/IdentityCofiberComponent:62-67`: only the general-n constructor |
| `KT/F/IdentityCofiberNormalization` | `F/IdentityCofiberNormalization:25-46`: both degree-one comparisons |

COL-0296 supplies the unchanged literal cofiber row/faces, chosen triangle,
identity suffix, canonical object-loop/transpose and actual prefix/component
transport. Its earlier transpose selections and suffix declarations are not
counted again. Existing native square-boundary, product/cylinder realization,
loop/fiber transposition and component-translation primitives are reused directly.

## References, registration and limits

The exact endpoint citations use existing key `quillen`, relation `adaptation`,
and the complete original source intervals above. One COL-0297 item binds the
boundary data and its application law, the quotient-fiber and split-prefix laws,
the whole left-prefix identification, the component constructor and both
degree-one comparisons. Lower helpers are not separate mathematical items.

Waldhausen, Section 1.3, definition of `S_n C` and face maps, pp. 328-329, is an
`ingredient` only at the categorical prism-face owner. It supplies the literal
interval-functor model and face direction, not the particular affine boundary
or reversed fiber-coordinate formulas. Thomason--Trobaugh 1.8.1-1.8.2, p. 263,
is optional background for the chosen zero-to-acyclic nullhomotopy; its classical
localization assumptions are not imported here. Hatcher is not a binding for
this item. No bibliography edit is needed.

This milestone asserts no scalar, polynomial, Laurent, supported-cone, fine-open
localization or terminal Bass boundary sign. Later original bodies do prove the
independent Laurent-unit comparison and actual scalar supported boundary. They
require further general and application inputs and are outside this native
slice; their existence is not an open source obligation of the present result.

## Preparation and validation boundary

At metadata preparation, the 27 new leaves, four overrides, three focused
regression leaves and proposed attributes had no native compilation evidence.
The author checked the selected source correspondence and reference scope;
`author_checked` records that comparison only. Static source checks do not
certify Lean elaboration, executed tests, axiom closure or Library export, and
independent review has its own evidence and checked span.

A validated-publication claim requires the exact integrated candidate's ordinary
native build, tests, applicable lint/axiom/Library checks and CI. Baseline or
COL-0296-candidate results alone do not validate these new sources. This page
records no local full-check or kernel-replay pass. The preparatory counts and
source cut describe this milestone, not a substitute for the final validation
record.

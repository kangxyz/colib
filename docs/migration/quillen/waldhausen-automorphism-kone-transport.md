# Original automorphism K-one and whole change-of-weak transport: COL-0299

This single milestone combines the actual weak-object composition homotopy,
independently defined K-one classes and complete nested-weak transport. It adapts
the selected original constructions at Quillen commit
[`c561118b7795eb9780be9ed391c3251d6a4d0afd`](https://github.com/kangxyz/quillen-k-theory/tree/c561118b7795eb9780be9ed391c3251d6a4d0afd).
The source cuts below identify the mathematical scope; the preparation evidence
is stated separately at the end.

## The actual weak-object composition cube

Let `{C : Type u} [Category.{v} C]`, `W : Structure C`, `f : A ⟶ B`,
`g : B ⟶ D`, `hf : W.weq f` and `hg : W.weq g`. The objects need not agree.
The three genuine nerve edges are the squares of `f`, `g` and `f ≫ g`.
The existing first edge and constant vertex triangles are supplemented by the
second and composite faces, both as entire grid functors and after realization.

Write `a,b,d` for the original object loops of `A,B,D`, and `P_f,P_g,P_fg`
for their specified `weakObjectSquareLoopPath` paths. The continuous cube
`C(r,s,t) = weakObjectCompositionCube f g hf hg (r,s,t)` retains independent
comparison time **r**, nerve/path time **s** and object-loop time **t**.
It evaluates the genuine realized nerve triangle on the original affine
standard-simplex path homotopy, using the actual inverse product-simplex map.

- At `r=0`, the original square of `f` is followed by that of `g` in **s**.
  The first branch includes `s ≤ 1/2` and uses `2*s`; the second uses `2*s-1`.
  Object-loop time `t` is unchanged in both branches.
- At `r=1`, it is the entire square of the literal composite `f ≫ g`.
- At `t=0` and `t=1`, it is the actual chosen basepoint for every `r,s`.
- At `s=0` and `s=1`, it is respectively `a(t)` and `d(t)` for every `r,t`.

Currying this cube gives the actual data

`weakObjectSquareCompositionTrack : (P_f.trans P_g).Homotopy P_fg`.

Its value at `(r,s)`, then `t`, is exactly `C(r,s,t)`. Both endpoints in
loop space are fixed throughout the comparison. A quotient-class identity or
an unspecified existence of homotopy would not supply this endpoint.
No zero-morphism instance is needed for this construction.

## Independent K-one classes and their multiplication

For a weak endomorphism `f : A ⟶ A`, the class is defined in the existing
homotopical `W.K 1` by

`Topology.loopKOneNormalization (W.kZeroObjectLoop A)
  (FundamentalGroup.fromPath ⟦W.weakObjectSquareLoopPath f hf⟧)`.

This normalizes the actual outer loop at its actual object-loop component.
It uses the existing inverse-prefix normalization, cancellation and degree
shift; it does not introduce another K-group or loop model.
`automorphismKOneClass` takes `e : A ≅ A` and applies this construction to
`e.hom` with its isomorphism weakness certificate.

The composition track proves the original order

`class(f ≫ g) = class(g) * class(f)`.

The identity class is `1`. The native monoid homomorphism is
`automorphismKOneHom A : Aut A →* W.K 1`. Native `Aut A` is a structure
with underlying isomorphism `e.asIso`, so its value is
`automorphismKOneClass e.asIso`. Multiplication uses `f.asIso.hom` followed
by `e.asIso.hom`, in exactly the order required by native automorphism
multiplication.

For `e : A ≅ B` intertwining weak endomorphisms by
`f ≫ e.hom = e.hom ≫ g`, the normalized classes agree. The proof uses
both specified composition homotopies to construct
`(P_f.trans P_e).Homotopy (P_e.trans P_g)`, then transports the actual
fundamental-group class along `P_e`. It does not assume all object components
are equal or replace the original path by an arbitrary connection.

### Native representation adaptations

Native Mathlib represents `FundamentalGroup X x` as
`End (FundamentalGroupoid.mk x)`. A group element is therefore built with
`FundamentalGroup.fromPath` from a path-homotopy quotient; its underlying
arrow is `.asHom`. Raw path quotients remain appropriate for genuine
fundamental-groupoid arrows. `End.ext` reduces the two new group-equality
proofs to those underlying arrows before quotient equality or conjugation.
The native formula
`p * q = .of (q.asHom.trans p.asHom)` preserves the displayed reversed
composition law.

Together with `Aut.asIso`, these are representation changes to five selected
constructions/proofs, not new mathematical premises. The native `Topology`
and `SSet` owners, `HomotopyGroup.map` and `GenLoop.postcomp` replace their
original implementation spellings without changing the maps.

## Canonical exact-functor naturality without strict zero preservation

Let `{C D : Type u} [Category.{v} C] [Category.{v} D]`,
`F : C ⥤ D`, and `hF : IsExact V.cof V.weq W.cof W.weq F`.
Both final assertions use the original canonical map:

`KMap hF 1 (V.weakEndomorphismKOneClass f hf) =
  W.weakEndomorphismKOneClass (F.map f) (hF.weak f hf)`;

`KMap hF 1 (V.automorphismKOneClass e) =
  W.automorphismKOneClass (F.mapIso e)`.

Neither statement assumes `F.obj V.zero = W.zero`. The strict intermediate
comparison retains that equality, the entire weak-square path and both endpoint
casts. Its proof uses whole bisimplex postcomposition, including all mixed grid
maps, not merely pointwise object agreement.

The unrestricted proof uses the actual
`rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)`.
It applies the strict theorem to `hF.rebase`, rewrites the public `KMap`
through its canonical definition, and uses the class-invariance theorem for
`e.app A` and the actual naturality equation `e.hom.naturality f`.
A theorem restricted to strict zero-preserving functors would lose this result.

Object and morphism universes remain independent. These exact-functor theorems
retain the original common `Type u` and `Category.{v}` for source and target;
the broader universe range of the exactness predicate alone does not widen the
simplicial-map and realization APIs used here.

## Whole fine-to-coarse transport

Let `N : NestedWeakEquivalences V`. Its actual data give equality of
cofibrations, equality of the chosen zeros and inclusion of fine weakness in
coarse weakness. The original `changeWeakMap N` is the realization of the
literal identity functor with `changeWeak_exact N`.

### Bisimplex families and weak-arrow squares

For arbitrary independent degrees `n,m`, retain the same literal grid
`F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C` and both fine/coarse certificates `hF,hG`.
The entire simplicial-family equation is

`bisimplexFamily V F hF ≫ sSetMap (changeWeak_exact N) =
  bisimplexFamily N.coarse F hG`.

For arbitrary independent barycentric points `z,t`, realization satisfies

`changeWeakMap N (bisimplexRealization V F hF (z,t)) =
  bisimplexRealization N.coarse F hG (z,t)`.

The weak-arrow specialization compares the whole fine square of `f` with the
coarse square of the same `f`, using `N.le_weq _ hf`. The categorical proof
retains mixed maps and the actual `N.zero_eq.symm`; both continuous coordinates
remain independent. No zero-morphism instance is required in this branch.

### Displayed cofiber triangle

Here retain `[HasZeroMorphisms C]`, the same `i : A ⟶ B`, `q : B ⟶ Q`,
both certificates `hi : V.cof i`, `hi' : N.coarse.cof i`, and both displayed
pushout certificates

`hQ : IsPushout i (0 : A ⟶ V.zero) q (0 : V.zero ⟶ Q)`;

`hQ' : IsPushout i (0 : A ⟶ N.coarse.zero) q (0 : N.coarse.zero ⟶ Q)`.

No weakness of `i` is required for this transport. The fine simplex maps to
the coarse simplex of this literal quotient, not an isomorphic replacement.
For every independent comparison time `r` and object-loop time `t`,

`changeWeakMap N (V.cofiberObjectLoopTrack i q hi hQ (r,t)) =
  N.coarse.cofiberObjectLoopTrack i q hi' hQ' (r,t)`.

### Prescribed identity suffix and all-degree component naturality

The identity-cofiber comparison uses the literal identity triangle and chosen
zero quotient. For every independent `s,t`,

`changeWeakMap N (V.identityCofiberSuffixPath A s t) =
  N.coarse.identityCofiberSuffixPath A s t`.

Thus the entire mapped suffix path agrees after its actual endpoint casts.
This is stronger than the earlier degree-one normalization equality of induced
transport maps. It does not identify the suffix itself with the standard
right-unit-removal path.

Write `g = basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)`.
Let `h_refl` be its actual constant-loop equation and `h_A` its actual
object-loop equation. For **every** `n : ℕ`, including zero, and every
`a : HomotopyGroup.Pi n (Path V.kBasepoint V.kBasepoint) (Path.refl V.kBasepoint)`,

`N.coarse.identityCofiberComponentEquiv A n (HomotopyGroup.map g h_refl a) =
  HomotopyGroup.map g h_A (V.identityCofiberComponentEquiv A n a)`.

The component equivalence remains the existing left-prefix equivalence followed
by transport along the prescribed identity suffix. Its naturality uses the whole
suffix equality and `Topology.pathTransport_naturality_of_track` at arbitrary
`n`. It is not inferred from a degree-one class calculation. The earlier
constructor and degree-one normalization remain the COL-0297 contribution;
only this new transport and naturality are counted here.

## Exact selected source and native ownership

The contribution adds **44 declarations** across **18 production paths**:
10 new leaves and eight extended or adjusted leaves. Two already-native
cofiber-simplex declarations move unchanged to their categorical owner and
are not counted as additions. Three focused test leaves contain 80 prepared
examples (20 categorical, 35 composition and 25 K-one/transport).

In the table, original paths start at `Quillen/Waldhausen/` at the pinned
commit and native paths start at `Colib/`. Every abbreviated module path ends
in `.lean`. `CT` means `CategoryTheory/Waldhausen/`, `KT` means
`KTheory/Waldhausen/`, `GC` means `GrothendieckComparison/`, `SC` means
`SConstruction/`, and `F` means `Fibration/`. Ranges include complete selected
bodies; excluded declarations in the same original files are not recounted.

| Native owner | New declarations | Original source selection |
| --- | ---: | --- |
| `CT/Rows/WeakObjectSimplex` | 2 | `GC/WeakObjectCompositionPrism:31-36`; `AutomorphismKOne:153-180` |
| `CT/SC/WeakObjectCompositionPrism` | 2 | `GC/WeakObjectCompositionPrism:57-75` |
| `CT/SC/BisimplexFamily` | 1 | `AutomorphismKOne:133-140` |
| `CT/SC/CofiberObjectSimplex` | 0; two moves | `GC/CofiberObjectTrack:30-44`, already native before this contribution |
| `CT/F/CofiberObjectChangeWeak` | 3 | `F/CofiberObjectChangeWeak:27-44`; `F/IdentityCofiberComponent:74-83` |
| `CT/F/BisimplexChangeWeak` | 2 | `F/BisimplexChangeWeak:30-36,49-62` |
| `KT/GC/CofiberObjectTrack` | 0 | Remove only the two moved declarations and replace their lower import |
| `KT/BisimplexRealization` | 1 | `AutomorphismKOne:142-151` |
| `KT/GC/WeakObjectCompositionRealization` | 2 | `GC/WeakObjectCompositionPrism:109-145` |
| `KT/GC/WeakObjectSquareTrack` | 2 | `AutomorphismKOne:43-50,87-92` |
| `KT/GC/WeakObjectCompositionCube` | 4 | `GC/WeakObjectCompositionCube:28-108` |
| `KT/GC/WeakObjectCompositionBased` | 4 | `GC/WeakObjectCompositionBased:77-105` |
| `KT/GC/WeakObjectCompositionTrack` | 4 | `GC/WeakObjectCompositionTrack:37-95` |
| `KT/GC/WeakObjectNaturality` | 2 | `AutomorphismKOne:182-209` |
| `KT/AutomorphismKOne` | 10 | `AutomorphismKOne:28-41,52-85,94-123,211-239` |
| `KT/F/CofiberObjectChangeWeak` | 1 | `F/CofiberObjectChangeWeak:46-56` |
| `KT/F/BisimplexChangeWeak` | 2 | `F/BisimplexChangeWeak:38-47,64-78` |
| `KT/F/IdentityCofiberComponent` | 2 | `F/IdentityCofiberComponent:85-145` |

The two unchanged moves are `Structure.cofiberObjectSimplex` and
`Structure.cofiberObjectSimplex_face`, including their docstrings and bodies.
Their new owner imports the actual `Rows/CofiberTwoFaces` and
`SConstruction/ObjectSimplex`; the realization owner imports that defining leaf.
Categorical change-weak results import the categorical owner directly.
There are no aliases or duplicate declaration sites. Existing continuous
cofiber constructions are unchanged.

The original prism, first realization face, constant vertex triangles and
`weakObjectSquareLoopPath` already have native owners from COL-0297. They
are reused rather than copied. The full original `IdentityCofiberNormalization`
was also already included there. The new composition track directly imports
both its based-cube owner and the existing square-path owner. The square-path
owner retains its lower dependency on composition realization. General
categorical transport depends on `AcyclicSubcategory`, not on realization or
K-theory. Ring and scheme applications do not enter these general owners.

## References and scope limits

A single COL-0299 item registers ten mathematical endpoints: the specified
composition track, reversed class composition, automorphism monoid homomorphism,
both unrestricted canonical KMap naturality theorems, full cofiber transport,
full bisimplex realization transport, full weak-square transport, full identity
suffix transport and all-degree component naturality. Supporting declarations
keep their ordinary native names, not separate permanent IDs.

Every new binding uses existing bibliography key `quillen`, relation
`adaptation`, and its exact original implementation interval. No new
bibliography key or broad classical theorem attribution is introduced.
The source correspondence concerns the actual selected implementation and
its native representation adaptations.

Independent `u,v` and realization universe `max u v` are retained throughout.
Only the cofiber and identity-suffix branches require zero morphisms. No
fibration theorem, weakness of the canonical acyclic-to-fiber comparison,
cylinder, connectivity, saturation, extension or factorization premise is
added. The new all-degree statement is component **naturality**, not an
all-degree extension of the earlier degree-one normalization comparison.

These are general inputs to later applications. No scalar-factorization,
Laurent-unit, supported-cone, fine-open localization, terminal boundary-sign,
Bass or nonconnective theorem is asserted by this item. The separate existence
of original application proofs does not enlarge this contribution's scope.

## Preparation and validation boundary

At metadata preparation, these 18 production paths, three regression leaves
and proposed COL-0299 attributes had no native compilation evidence. The
selected source bodies and reference scope were compared with the original;
`author_checked` records that source correspondence only. Static inventories,
source comparisons and import-graph checks do not certify elaboration,
executed tests, axiom closure or native Library export. Independent mathematical
review has separate evidence and a separately identified checked span.

A validated-publication claim requires the exact integrated candidate's
ordinary native build, tests, applicable lint, axiom and Library checks and CI.
Evidence for earlier items or a different candidate does not validate these
additions. This historical preparation record claims no native check, local
full-check or kernel-replay pass for this milestone.

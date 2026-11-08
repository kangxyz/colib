# Coarse exactness of the original joint cylinder

COL-0306 is a general Waldhausen result owned by
`Colib/CategoryTheory/Waldhausen/Fibration/Rows/CoarseJoint.lean`.
Its input is the existing `JointData N`, not a new cylinder or factorization
structure. Its output is `JointData (NestedWeakEquivalences.refl N.coarse)`.
The input is exact for the fine arrow and extension structures; only its
projection is assumed coarse-weak. The output therefore needs a genuine
proof of coarse exactness.

## Construction and hypotheses

Let `C : Type u` have `Category.{v} C`, let `V` be its Waldhausen structure,
and let `N : NestedWeakEquivalences V`. Object and morphism universes remain
independent. The nested data retain the common cofibration class and chosen
zero, together with inclusion of fine weak equivalences into coarse ones.

1. The original endpoint coproduct is a pushout over the actual coarse
   chosen zero. Coarse gluing then proves that the original joint source map
   is weak whenever both endpoint maps are coarse-weak. This step does not
   require two-out-of-three.
2. Under coarse two-out-of-three, the original projection naturality square
   proves that the original middle map is coarse-weak whenever the target
   component is coarse-weak. No source weakness is required for this step.
3. Native `ExtensionCategory.postcompose` for `changeWeak_exact N` changes
   the cofibration certificate, retaining the literal joint arrow and maps.
   Its exactness transports zero objects, genuine Reedy cofibrations and
   actual pushouts. The first two steps provide the missing coarse weak-map
   preservation.
4. `JointData.coarseReflexive` packages this coarse-exact functor with the
   original two endpoint transformations, coproduct witnesses, projection,
   factorization equation and weak projection proof.

The supporting simp lemmas identify both endpoint components, projection,
joint arrow, and both components of every joint map. The regression checks
also identify the entire source and middle functors and the entire endpoint
and projection natural transformations. Existing `factorizationOfJointData`
then gives the actual coarse quotient-row factorization, retaining every
original inclusion and projection component.

## Source correspondence

The implementation source is
[Quillen at c561118b7795eb9780be9ed391c3251d6a4d0afd](https://github.com/kangxyz/quillen-k-theory/tree/c561118b7795eb9780be9ed391c3251d6a4d0afd).
The exact source file is
`Quillen/Waldhausen/Fibration/Rows/CoarseJoint.lean`.
Both public endpoints have precise compiled references to this existing
bibliographic record. These are implementation correspondence claims, not
attributions of a new localization theorem to the literature.

| Quillen span | Native declaration | Preserved mathematical content |
| --- | --- | --- |
| 30–38 | `jointSource_coarse_isPushout` | Actual endpoint coproduct over the coarse zero |
| 41–48 | `jointSource_coarseWeak` | Coarse gluing with both endpoint weak maps |
| 53–58 | `jointMiddle_coarseWeak` | Actual projection square and target weakness |
| 61–62 | `coarseJoint` | Identity postcomposition on the original joint arrow |
| 65–86 | `coarseJoint_exact` | Zero, cofibration, coarse weakness and pushout preservation |
| 90–98 | `JointData.coarseReflexive` | Genuine reflexive coarse data with all original fields |
| 101–114 | `coarseReflexive_inl`, `coarseReflexive_inr`, `coarseReflexive_projection`, `coarseReflexive_joint_hom` | Literal endpoint, projection and joint-arrow identities |
| Native supporting lemmas | `coarseReflexive_joint_map_left`, `coarseReflexive_joint_map_right` | Literal source and middle map identities |

The existing native exact extension postcomposition and row factorization
are reused. No `JointRetarget` wrapper, replacement mathematical object,
Aglib import or Quillen production import is introduced.

## Regression scope and remaining work

`ColibTest.WaldhausenCoarseJoint` checks the two distinct weak-map arguments,
actual endpoint and mapped pushouts, full coarse exactness, literal functors
and natural transformations, actual cofibrations, and the existing row
factorization with unchanged components.

`ColibTest.PerfectOpenCoarseJoint` specializes the result to the actual
`perfectOpenJointData` for an arbitrary open immersion. It retains the native
perfect-complex full subcategory, ambient monomorphism cofibrations, original
identity-cone middle and joint inclusion, actual projection, proved second
endpoint section and row projection. It supplies no geometric finiteness,
approximation or extra exactness hypotheses. Geometry appears only in this
regression, never in the general owner.

This contribution is a prerequisite for later approximation and localization
work. It proves neither dual approximation nor fine-open localization,
surjectivity of fine open restriction on K-zero, a new fiber comparison,
or a nonconnective result. There are no new topological homotopies in this
source span; existing downstream constructions and their whole homotopies
are unchanged.

Local compilation, author source correspondence, independent mathematical
review and remote lint/axiom checks are separate evidence. The catalog's
`author_checked` field records only the source comparison above.

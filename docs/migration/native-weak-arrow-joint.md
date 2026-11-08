# Coherent joint data on native opposite weak arrows

## Mathematical scope

COL-0310 constructs genuine `JointData` on the literal opposite of the weak-arrow
category. The underlying category is the full subcategory of Mathlib's actual
functor comma category whose stored morphism F(A) → B belongs to the given weak
class. Its objects and morphisms are not replaced by an equivalent model.

The inputs are the original exact functor F, exactness of F.op between the given
dual structures, compatible duality on the target, two actual component joint
functors with their exactness and endpoints, a natural isomorphism

Tc.joint ⋙ postcompose ≅ F.op.mapArrow ⋙ Td.joint,

and the three original equations identifying the left inclusion, right
inclusion and projection. Naturality of an arbitrary isomorphism alone does not
imply these endpoint equations. Their hypotheses remain explicit.

The original reversed weak square is mapped by the target joint functor and
composed with the inverse of this natural isomorphism. Compatible duality
converts its weak component maps back to membership of the original stored
weak arrow. This constructs actual source and middle functors, a genuine
componentwise cofibration, and the original extension-valued joint functor.

Exactness is proved, not assumed. Exact component projections detect zeros and
actual pushouts. The relative cofibration proof applies the actual mapped
relative pushout criterion to both projections. A new heterogeneous-family
lemma and its pair form preserve the original hypotheses, including independent
source and target universes. The pair targets need not even share universe
bounds. Ordinary pointwise cofibrancy would not suffice for this Reedy condition.

The whole natural endpoint maps retain the specified component inclusions and
projection. Reflected component coproducts give the actual endpoint coproduct.
The original arrow is exactly the composite of the first endpoint, the joint
cofibration and the weak projection. These data produce `JointData` for the
reflexive dual weak-arrow structure without extra factorization assumptions.

## Literal maps and chosen cofibers

The source and middle functors and both full component joint functors satisfy
the original literal projection equalities. The component cofibration arrows,
every component of each mapped square, both endpoint inclusions and the weak
projection are unchanged; in-package tests check their definitional equations.

This is not a statement that a projection strictly preserves an independently
chosen cofiber object. Applying the component cofiber functor *after* the proved
component equality gives the corresponding functor equality, which is also
tested. A comparison between independently chosen cofibers would instead require
the genuine canonical isomorphism. No such additional assertion is made here.

## Source crosswalk and references

Original implementation: Quillen commit
c561118b7795eb9780be9ed391c3251d6a4d0afd. Source attribution and the bibliography's
`quillen` record identify this exact implementation, rather than attributing
this precise coherent construction to an unchecked external theorem.

| Original Quillen/Waldhausen source | Native Colib/CategoryTheory/Waldhausen owner | Retained result |
| --- | --- | --- |
| ArrowCategory/Exact.lean | ArrowCategory/Exact.lean | Exactness of the actual mapArrow functor in independent universes |
| ExtensionCategory/HeterogeneousDetection.lean | ExtensionCategory/HeterogeneousDetection.lean | Original heterogeneous family and different-target pair detection for genuine relative cofibrations |
| WeakArrow/JointFunctor.lean | WeakArrow/JointFunctor.lean | Stored reversed weak square, actual source/middle objects, original cofibration, joint functor and literal component equalities |
| WeakArrow/JointEndpoints.lean | WeakArrow/JointEndpoints.lean | Three explicit endpoint coherence equations, natural endpoint maps, original factorization and literal projection formulas |
| WeakArrow/JointExact.lean | WeakArrow/JointExact.lean | Exactness through actual zeros, mapped relative cofibrations and pushouts |
| WeakArrow/JointData.lean | WeakArrow/JointData.lean | Genuine reflexive dual JointData with the reflected endpoint coproduct |

The entire mathematical content of these six original modules is retained.
Only native imports/namespaces, documentation, reference annotations and spacing
are changed. The existing native PostcomposeDetection.mapped_relative_cof is
reused; the extension category is not redefined. Every production owner is
categorical and imports no K-theory or algebraic-geometry application owner.
Production imports only Colib and its pinned Mathlib/Stacks dependencies, never
Quillen or Aglib.

COL-0309 supplies the original comma and weak-arrow structures, exact component
projections and dual detection. COL-0308 supplies the structural compatible-dual
interface. The source snapshot also retains the exact COL-0306 and COL-0308
prerequisite files. They have separate ownership and are not claimed as new work.

## Scope boundaries and verification

The generic natural isomorphism is an input, not a proof of any scheme-specific
joint-cylinder compatibility. Natural isomorphisms for opposite complexes,
native perfect complexes, geometric incoming lifts, fine localization and K-map
conclusions are outside this contribution. No false comparison, cylinder or
factorization assumption is added to replace the original construction.

WaldhausenHeterogeneousDetection tests both detection forms, with independent
universe variables. WaldhausenWeakArrowJoint checks stored maps, full component
functors, exactness, the original cofibration, both components of each square,
endpoint maps, coproduct and factorization. Local compilation and exact
source/artifact checks are separate from independent mathematical review and
remote native lint, axiom and Library checks.

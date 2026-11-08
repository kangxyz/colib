# Native forward scalar supported boundary

## Scope

COL-0304 identifies the original relative connecting map on the independently defined
forward scalar K-one class with the actual supported signed mapping-cone K-zero class.
The data are an arbitrary open immersion `j : U → X`, a native perfect complex `K`, a
global scalar `r` on `X`, a specified unit `q` on `U`, and `j.appTop r = q`.
No compactness, separation, Noetherianity, regularity, or nonzerodivisor hypothesis is added.

The source is Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Its relevant endpoint is
`Quillen/AlgebraicGeometry/PerfectComplexes/ScalarSupportedBoundary.lean:35-48`.
The later fine-open, rank-one, Laurent, Mayer–Vietoris, and Bass conclusions are not included.
In particular the positive relative scalar-cone class is not the later T-first Bass sign.

## Definitions and proof route

The geometric provider is the native scalar cofiber of COL-0303, with its literal inclusion,
weak projection, genuine chosen-zero pushout, and quotient-preserving signed-cone isomorphism.
It uses the existing native category with ambient monomorphism cofibrations and
quasi-isomorphisms. It does not replace it by the older split-exact subcategory model.

`PerfectScalarKOne` defines the forward class using the actual scalar weak-arrow square and
the existing `Topology.loopKOneNormalization`. The definition has no cofiber, homotopy-fiber,
or connecting-map input. The remaining modules retain the full original prism and both
path coordinates through the fine source path, iterated fiber, and geometric pasting.
The cofiber boundary loop is the inverse of that forward square at the original object-loop
component. The actual inverse-prefix cancellation and identity-cofiber component equivalence
then put both loops in the same original K-one group.

The existing `connectingHom_loop_path` retains the second inverse coming from the
coordinate transposition. The proof cancels the two inverses and transports the resulting
actual cofiber object class through the original acyclic-to-supported exact functor.
Thus the endpoint is the positive class of `CochainComplex.mappingCone` of the original
scalar chain map, with its original signed quotient map.

The canonical-fiber object-class calculation is generic and has been placed in
`Colib.KTheory.Waldhausen.Fibration.CanonicalFiberObjectClass`, with independent
object and morphism universes. No general Topology source or mathematical model is duplicated.

## Source correspondence

All paths below are relative to `Quillen/AlgebraicGeometry/PerfectComplexes/`.

| Original source | Retained content |
| --- | --- |
| `ScalarCofiberPrism.lean:96-130` | Actual composition cube, reversed zero face, and based-loop family |
| `ScalarCofiberChangeWeak.lean:35-80` | Fine triangle track and its original coarse image |
| `ScalarCofiberSourcePath.lean:36-79` | Actual weak projection and fine return path |
| `ScalarCofiberIteratedFiber.lean:36-93` | Exact iterated-fiber point and reversed mapped source path |
| `ScalarCofiberPasting.lean:37-131` | Prefix, original weak scalar loop, and complete triangle pasting |
| `ScalarCofiberBoundaryOrientation.lean:37-83` | Actual homotopy to the inverse forward scalar loop |
| `ScalarCofiberFiberBoundaryPath.lean:37-59` | Actual iterated-fiber deformation path |
| `ScalarCofiberKOneNormalization.lean:80-155` | Normalized path, component comparison, and inverse class |
| `ScalarCofiberFiberComponent.lean:44-108` | Identity suffix transport and original fiber component |
| `ScalarForwardRelativeBoundary.lean:36-162` | Normalization and the cancellation of both inverse signs |
| `ScalarSupportedBoundary.lean:35-48` | Original connecting homomorphism and actual supported object class |

The source normalization definitions at lines 47-77 are consumed through their already
migrated general `Topology.loopKOneNormalization` and cancellation, not copied into a second
scalar-specific model. `CanonicalFiberObjectClass` extracts the original lines 121-134 of
`ScalarForwardRelativeBoundary.lean` to its generic owner.

## Validation contract

The in-package regression module is `ColibTest.PerfectScalarSupportedBoundary`.
It checks the independent input class, the intermediate inverse, the positive original
supported boundary, the literal signed cone and quotient, and the generic universe range.
Compilation receipts identify exact source hashes and all five Lean artifact families;
source comparison, compilation, and independent review remain separate facts.

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.TensorParameterInsertion
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusChainCoordinate

/-! # A natural coordinate insertion into the actual simplicial tensor

The original parameter map is obtained by composing the natural insertion
with the actual AW right leg, degree by degree.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry.Scheme AlgebraicTopology
open scoped Simplicial TensorProduct
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
local notation "G" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))

/-- The original universal coordinate, as a reduced weight-one section. -/
def reducedTorusUniversalCoordinate : (reducedTorusIntPresheaf k 1).obj (op G) :=
  (toReducedTorus k 1).hom.app (op (Cor.mk G))
    (ULift.up ((Cor.graphFunctor k).map
      (SmoothSite.torusPowerOneIso (Spec (CommRingCat.of k))).inv))

/-- The simplicial insertion uses the native parameter swap and is natural in
both smooth sources and all simplex maps. -/
def reducedTorusSimplicialCoordinateInsertion (q : ℕ) :=
  AlgebraicSimplex.simplicialTensorParameterInsertion k
    (reducedTorusIntPresheaf k q) (reducedTorusIntPresheaf k 1) G
    (reducedTorusUniversalCoordinate k)

/-- The actual parameter insertion into the diagonal tensor chain complex. -/
def reducedTorusChainCoordinateInsertion (q : ℕ) :
    (alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q) ⟶
      ((AlgebraicSimplex.parameterReindex k (A := _ ) G).mapHomologicalComplex (.down ℕ)).obj
        ((alternatingFaceMapComplex _).obj
          (reducedTorusIntSimplicial k q ⊗ reducedTorusIntSimplicial k 1)) :=
  AlgebraicSimplex.chainTensorParameterInsertion k
    (reducedTorusIntPresheaf k q) (reducedTorusIntPresheaf k 1) G
    (reducedTorusUniversalCoordinate k)

/-- Composing the actual insertion with the actual pairing gives the original
singular parameter product in every degree, including its last-factor swap. -/
theorem reducedTorusChainCoordinateInsertion_pairing
    (U : SmoothSite (Spec (CommRingCat.of k))) (q n : ℕ)
    (s : sections (reducedTorus k q)
      (Cor.mk (SmoothSite.product U (AlgebraicSimplex.smoothSiteObj k n)))) :
    (((reducedTorusPresheafChainPairing k q).f n).app (op (SmoothSite.product U G))).hom
      ((((reducedTorusChainCoordinateInsertion k q).f n).app (op U)).hom s) =
      ((reducedTorusSingularParameterProduct k q).f n).app (op U) s := by
  change (((reducedTorusPresheafChainPairing k q).f n).app
    (op (SmoothSite.product U G))).hom
    ((((AlgebraicSimplex.chainTensorParameterInsertion k
      (reducedTorusIntPresheaf k q) (reducedTorusIntPresheaf k 1) G
      (reducedTorusUniversalCoordinate k)).f n).app (op U)).hom s) = _
  rw [AlgebraicSimplex.chainTensorParameterInsertion_f_app]
  change (((reducedTorusPresheafChainPairing k q).f n).app
    (op (SmoothSite.product U G))).hom
    (transfer (reducedTorus k q) ((Cor.graphFunctor k).map
      (SmoothSite.productMap (SmoothSite.productFst U G)
        (𝟙 (AlgebraicSimplex.smoothSiteObj k n)))) s ⊗ₜ[ℤ]
      transfer (reducedTorus k 1) ((Cor.graphFunctor k).map
        (SmoothSite.productFst (SmoothSite.product U G) (AlgebraicSimplex.smoothSiteObj k n) ≫
          SmoothSite.productSnd U G))
      ((toReducedTorus k 1).hom.app (op (Cor.mk G)) (ULift.up _))) = _
  let D := AlgebraicSimplex.smoothSiteObj k n
  let V := SmoothSite.product (SmoothSite.product U G) D
  let f := SmoothSite.productMap (SmoothSite.productFst U G) (𝟙 D)
  let g := SmoothSite.productFst (SmoothSite.product U G) D ≫ SmoothSite.productSnd U G
  let e := SmoothSite.torusPowerOneIso (Spec (CommRingCat.of k))
  have h := reducedTorus_transfer_apply k 1 ((Cor.graphFunctor k).map g)
    ((Cor.graphFunctor k).map e.inv)
  have hg := (Cor.graphFunctor k).map_comp g e.inv
  have h' := h.trans (congrArg
    (fun z => (toReducedTorus k 1).hom.app (op (Cor.mk V)) (ULift.up z)) hg.symm)
  exact (congrArg (fun b =>
    (((reducedTorusPresheafChainPairing k q).f n).app
      (op (SmoothSite.product U G))).hom
      (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f) s ⊗ₜ[ℤ] b)) h').trans
    (reducedTorusPresheafChainPairing_coordinate k U q n s)
/-- Every component of the actual composite chain map is the original parameter
map, after forgetting only the canonical integer-linear structure. -/
theorem reducedTorusChainCoordinateInsertion_comp_f_app
    (U : SmoothSite (Spec (CommRingCat.of k))) (q n : ℕ) :
    (((reducedTorusChainCoordinateInsertion k q ≫
      ((AlgebraicSimplex.parameterReindex k (A := _) G).mapHomologicalComplex
        (.down ℕ)).map (reducedTorusPresheafChainPairing k q)).f n).app
          (op U)).hom.toAddMonoidHom =
      (((reducedTorusSingularParameterProduct k q).f n).app (op U)).hom := by
  ext s
  exact reducedTorusChainCoordinateInsertion_pairing k U q n s
end AlgebraicGeometry.PresheafWithTransfers

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSimplicialTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.FlatEilenbergZilber

/-!
# The objectwise Alexander–Whitney span

The two arrows have the same actual source chain complex.
The AW arrow points toward the ordinary total tensor, not away from it.
No inverse chain map, K-flatness, or derived tensor comparison is asserted.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry.Scheme AlgebraicTopology
open scoped Simplicial TensorProduct
universe u
namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]
variable (U : SmoothSite (Spec (CommRingCat.of k)))

/-- Evaluation of the existing literal singular simplicial presheaf at U. -/
def reducedTorusEvaluatedSimplicial (q : ℕ) : SimplicialObject (ModuleCat.{u + 1} ℤ) :=
  reducedTorusIntSimplicial k q ⋙
    (evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ) (ModuleCat.{u + 1} ℤ)).obj (op U)

/-- Evaluation commutes with the actual pointwise simplicial tensor. -/
def reducedTorusEvaluateTensorIso (q : ℕ) :
    (reducedTorusIntSimplicial k q ⊗ reducedTorusIntSimplicial k 1) ⋙
      (evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
        (ModuleCat.{u + 1} ℤ)).obj (op U) ≅
    reducedTorusEvaluatedSimplicial k U q ⊗ reducedTorusEvaluatedSimplicial k U 1 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [reducedTorusEvaluatedSimplicial])

/-- The evaluated original tensor pairing, transported only by evaluation's
pointwise tensor comparison. -/
def reducedTorusEvaluatedTensorProduct (q : ℕ) :
    reducedTorusEvaluatedSimplicial k U q ⊗ reducedTorusEvaluatedSimplicial k U 1 ⟶
      reducedTorusEvaluatedSimplicial k U (q + 1) :=
  (reducedTorusEvaluateTensorIso k U q).inv ≫
    Functor.whiskerRight (reducedTorusSimplicialTensorProduct k q)
      ((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
        (ModuleCat.{u + 1} ℤ)).obj (op U))

/-- The right arrow of the actual objectwise chain span. -/
def reducedTorusObjectwiseChainPairing (q : ℕ) :
    (alternatingFaceMapComplex (ModuleCat.{u + 1} ℤ)).obj
      (reducedTorusEvaluatedSimplicial k U q ⊗ reducedTorusEvaluatedSimplicial k U 1) ⟶
    (alternatingFaceMapComplex (ModuleCat.{u + 1} ℤ)).obj
      (reducedTorusEvaluatedSimplicial k U (q + 1)) :=
  (alternatingFaceMapComplex _).map (reducedTorusEvaluatedTensorProduct k U q)

/-- The left arrow of the span: degreewise-tensor chains to ordinary total tensor. -/
def reducedTorusObjectwiseAW (q : ℕ) :
    (alternatingFaceMapComplex (ModuleCat.{u + 1} ℤ)).obj
      (reducedTorusEvaluatedSimplicial k U q ⊗ reducedTorusEvaluatedSimplicial k U 1) ⟶
    HomologicalComplex.tensorObj
      ((alternatingFaceMapComplex (ModuleCat.{u + 1} ℤ)).obj
        (reducedTorusEvaluatedSimplicial k U q))
      ((alternatingFaceMapComplex (ModuleCat.{u + 1} ℤ)).obj
        (reducedTorusEvaluatedSimplicial k U 1)) :=
  alexanderWhitney _ _

/-- Native no-flat Eilenberg–Zilber applies to the actual evaluated modules.
This does not identify ordinary total tensor with derived tensor. -/
instance reducedTorusObjectwiseAW_quasiIso (q : ℕ) :
    QuasiIso (reducedTorusObjectwiseAW k U q) := by
  dsimp [reducedTorusObjectwiseAW]
  infer_instance

end AlgebraicGeometry.PresheafWithTransfers

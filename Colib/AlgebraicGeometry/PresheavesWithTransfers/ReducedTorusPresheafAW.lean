/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusObjectwiseAW
public import Mathlib.Algebra.Homology.Functor

/-!
# The presheaf chain span and evaluation of its common source

These are actual presheaf chain maps. No claim that the
presheaf AW map is a quasi-isomorphism is made here: its evaluated target still
requires the coproduct/total-tensor comparison.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry.Scheme AlgebraicTopology
open scoped Simplicial TensorProduct
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]

/-- The actual pointwise tensor of integral presheaves is additive in both variables. -/
instance integralPresheafMonoidalPreadditive :
    MonoidalPreadditive ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤
      ModuleCat.{u + 1} ℤ) where
  whiskerLeft_zero := by intros; apply NatTrans.ext; funext U; simp
  zero_whiskerRight := by intros; apply NatTrans.ext; funext U; simp
  whiskerLeft_add := by intros; apply NatTrans.ext; funext U; simp
  add_whiskerRight := by intros; apply NatTrans.ext; funext U; simp

/-- Apply the native chain functor to the actual simplicial presheaf pairing. -/
def reducedTorusPresheafChainPairing (q : ℕ) :
    (alternatingFaceMapComplex _).obj
      (reducedTorusIntSimplicial k q ⊗ reducedTorusIntSimplicial k 1) ⟶
    (alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k (q + 1)) :=
  (alternatingFaceMapComplex _).map (reducedTorusSimplicialTensorProduct k q)

/-- Native AW in the presheaf category, with its true ordinary total-tensor target. -/
def reducedTorusPresheafAW (q : ℕ) :
    (alternatingFaceMapComplex _).obj
      (reducedTorusIntSimplicial k q ⊗ reducedTorusIntSimplicial k 1) ⟶
    HomologicalComplex.tensorObj
      ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q))
      ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k 1)) :=
  alexanderWhitney _ _

variable (U : SmoothSite (Spec (CommRingCat.of k)))

/-- Evaluation of the original chain complex, using native additive-functor
compatibility of the alternating face map construction. -/
def reducedTorusEvaluateChainsIso (q : ℕ) :
    (((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
      (ModuleCat.{u + 1} ℤ)).obj (op U)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q)) ≅
    (alternatingFaceMapComplex _).obj (reducedTorusEvaluatedSimplicial k U q) :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
    ((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
      (ModuleCat.{u + 1} ℤ)).obj (op U))).app (reducedTorusIntSimplicial k q)

/-- The source comparison uses only evaluation of chains and the already
verified pointwise tensor comparison. It does not invert AW. -/
def reducedTorusEvaluateTensorChainsIso (q : ℕ) :
    (((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
      (ModuleCat.{u + 1} ℤ)).obj (op U)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((alternatingFaceMapComplex _).obj
        (reducedTorusIntSimplicial k q ⊗ reducedTorusIntSimplicial k 1)) ≅
    (alternatingFaceMapComplex _).obj
      (reducedTorusEvaluatedSimplicial k U q ⊗ reducedTorusEvaluatedSimplicial k U 1) :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
    ((evaluation ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ)
      (ModuleCat.{u + 1} ℤ)).obj (op U))).app
        (reducedTorusIntSimplicial k q ⊗ reducedTorusIntSimplicial k 1) ≪≫
    (alternatingFaceMapComplex _).mapIso (reducedTorusEvaluateTensorIso k U q)

end AlgebraicGeometry.PresheafWithTransfers

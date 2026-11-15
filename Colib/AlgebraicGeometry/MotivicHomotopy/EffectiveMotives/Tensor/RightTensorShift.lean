/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.LefschetzComparison
public import Colib.CategoryTheory.Triangulated.SignedShift

/-! # The signed right tensor comparison in effective motives -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Preadditive MonoidalCategory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)] [MonoidalPreadditive (Cor k)]

local notation "E" => EffectiveMotivesMinus k

/-- The abelian structure of the transfer sheaves used for right tensor shift compatibility. -/
local instance rightTensorShiftAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

variable (e : ∀ X : SmoothSite (Spec (CommRingCat.of k)),
  Cor.graphFunctor k ⋙ (curriedTensor (Cor k)).flip.obj (Cor.mk X) ≅
    SmoothSite.Contraction.parameterProduct X ⋙ Cor.graphFunctor k)

set_option maxHeartbeats 750000 in
-- The signed interchange equation concerns the actual effective shift.
/-- Shifting the fixed right argument compares the native right tensor shifts with
the signed shift of its value. The sign is the two-variable interchange sign. -/
theorem effectiveTensorRightShiftIso_commShift (L : E) (n : ℤ) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionCommShift₂Int e
    NatTrans.CommShift (effectiveTensorRightShiftIso e L n).hom ℤ := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionCommShift₂Int e
  let B := curriedTensor E
  refine ⟨fun m => NatTrans.ext (funext fun X => ?_)⟩
  have h := B.commShift₂_comm CommShift₂Setup.int X L m n
  let a := ((tensorLeft (X⟦m⟧)).commShiftIso n).hom.app L
  let b := ((tensorRight L).commShiftIso m).hom.app X
  let c := ((tensorRight (L⟦n⟧)).commShiftIso m).hom.app X
  let d := ((tensorLeft X).commShiftIso n).hom.app L
  let Z := X ⊗ L
  let f := shiftComm Z m n
  let u := (m * n).negOnePow
  change a ≫ b⟦n⟧' = c ≫ d⟦m⟧' ≫ f.inv ≫
    ((CommShift₂Setup.int (D := E)).ε m n).val.app (Z⟦m⟧⟦n⟧) at h
  rw [CommShift₂Setup.int_ε, CatCenter.app_neg_one_zpow,
    Linear.comp_units_smul, Category.comp_id] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app]
  change c ≫ d⟦m⟧' = a ≫ b⟦n⟧' ≫
    ((shiftFunctor E n).commShiftIso m).hom.app Z
  have hu : ((shiftFunctor E n).commShiftIso m).hom.app Z = u • f.hom := by
    change ((signedShiftComm E n m).hom.app Z) = _
    simp only [signedShiftComm, NatIso.ofComponents_hom_app, smul_iso_hom, mul_comm n m]
    rfl
  rw [hu, ← Category.assoc a, h]
  simp only [Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul,
    f.inv_hom_id, smul_smul]
  change c ≫ d⟦m⟧' = (u * u) • (c ≫ d⟦m⟧' ≫ 𝟙 _)
  rw [Int.units_mul_self, one_smul]
  exact (Category.comp_id _).symm.trans (Category.assoc _ _ _)

end AlgebraicGeometry.MotivicHomotopy

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.Boundary.Representatives
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.ConiveauObject

/-!
# Agreement of the coniveau connecting maps

On a coniveau window, the spectral object boundary is the original
localization boundary followed by the map from the support stage to the
next window.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme TopologicalSpace

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

private theorem boundary_comp_of_generators {C : Type*} [Category* C]
    {A D E P R Q : C}
    (j : A ⟶ D) (M : D ⟶ Q) (B : D ⟶ R) (S : R ⟶ Q)
    (δ : A ⟶ E) (β : A ⟶ P) (ρ : P ⟶ E) (i : E ⟶ Q) (t : P ⟶ R)
    (hM : j ≫ M = δ ≫ i) (hB : j ≫ B = β ≫ t)
    (hS : t ≫ S = ρ ≫ i) (hδ : δ = β ≫ ρ) :
    j ≫ M = j ≫ B ≫ S := by
  have hleft : j ≫ M = β ≫ ρ ≫ i :=
    hM.trans ((congrArg (· ≫ i) hδ).trans (Category.assoc _ _ _))
  have hright : j ≫ B ≫ S = β ≫ ρ ≫ i :=
    (Category.assoc j B S).symm.trans
      ((congrArg (· ≫ S) hB).trans
        ((Category.assoc β t S).trans (congrArg (β ≫ ·) hS)))
  exact hleft.trans hright.symm

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))
local notation "DM(" field ")" => EffectiveMotivesMinus field

variable (X : Sm(k))
  [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The transfer-sheaf abelian structure used in comparing the window boundaries. -/
local instance coniveauBoundaryAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

variable [UnivLE.{u, w'}]

set_option maxHeartbeats 900000 in
-- Use the two original colimit generator identities on the flag with empty smallest support.
/-- The spectral connecting map is the original window boundary followed by the stage map. -/
theorem coniveauWindowConnecting_eq_boundary (K : DM(k)) (n : ℤ) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    coniveauWindowConnecting k X K n (n + 1) rfl hab hbc =
      coniveauWindowBoundary k X K n hab ≫ coniveauCohomologyToWindow k X K (n + 1) b c := by
  apply colimit.hom_ext
  intro ZW
  let T : ConiveauSupportTriples k X a b c := ⟨(⊥, ZW.1.1, ZW.1.2), bot_le, ZW.2⟩
  let A := coniveauEmptySupportPair k X (b := c) ZW.1.1
  let j := colimit.ι (coniveauRelativeSupportDiagram k X K n a b) ZW
  let M := coniveauWindowConnecting k X K n (n + 1) rfl hab hbc
  let B := coniveauWindowBoundary k X K n hab
  let S := coniveauCohomologyToWindow k X K (n + 1) b c
  let δ := coniveauEmptyFlagBoundary k X K n (c := c) ZW
  let β := (coniveauRelativeSupportBoundary k X K n a b).app ZW
  let ρ := (coniveauRelativeSupportRestriction k X K (n + 1) b c).app A
  let i := colimit.ι (coniveauRelativeSupportDiagram k X K (n + 1) b c) A
  let t := colimit.ι (coniveauCohomologyDiagram k X K (n + 1) b) ZW.1.1
  have hM : j ≫ M = δ ≫ i := by
    unfold δ coniveauEmptyFlagBoundary
    exact ι_coniveauWindowConnecting k X K n (n + 1) rfl hab hbc T
  have hB : j ≫ B = β ≫ t := ι_coniveauWindowBoundary k X K n hab ZW
  have hS : t ≫ S = ρ ≫ i := ι_coniveauCohomologyToWindow k X K (n + 1) A
  have hδ : δ = β ≫ ρ := closedSupportSpectralObject_δ_bot k X K n (c := c) ZW
  change j ≫ M = j ≫ B ≫ S
  exact boundary_comp_of_generators j M B S δ β ρ i t hM hB hS hδ

end AlgebraicGeometry.MotivicHomotopy

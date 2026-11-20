/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Basic
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.WindowColimits
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata.OpenPairs
import all Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Basic

/-!
# Absolute coniveau stages in relative windows

The original stage maps commute with weakening the window bounds.
Once the second codimension bound exceeds the dimension, the original
stage map is an isomorphism onto the window.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable (X : Sm(k))

/-- A closed support regarded as a nested pair with empty smaller support. -/
def coniveauEmptySupportPair {a b : ℕ} (W : ConiveauSupports k X a) :
    ConiveauSupportPairs k X a b :=
  ⟨(⊥, W), bot_le⟩

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "DM(" field ")" => EffectiveMotivesMinus field

/-- The transfer-sheaf abelian structure used in comparing absolute stages and windows. -/
local instance coniveauAbsoluteWindowsAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

private theorem generator_square {C : Type*} [Category* C] {A B D D' E E' : C}
    (i : A ⟶ D) (i' : A ⟶ D') (j : B ⟶ E) (j' : B ⟶ E')
    (R : D ⟶ E) (R' : D' ⟶ E') (S : D ⟶ D') (M : E ⟶ E')
    (ρ ρ' : A ⟶ B)
    (hR : i ≫ R = ρ ≫ j) (hR' : i' ≫ R' = ρ' ≫ j')
    (hS : i ≫ S = i') (hM : j ≫ M = j') (hρ : ρ = ρ') :
    i ≫ R ≫ M = i ≫ S ≫ R' := by
  have hL : i ≫ R ≫ M = ρ ≫ j' :=
    (Category.assoc i R M).symm.trans
      ((congrArg (· ≫ M) hR).trans
        ((Category.assoc ρ j M).trans (congrArg (ρ ≫ ·) hM)))
  have hT : i ≫ S ≫ R' = ρ' ≫ j' :=
    (Category.assoc i S R').symm.trans
      ((congrArg (· ≫ R') hS).trans hR')
  exact hL.trans ((congrArg (· ≫ j') hρ).trans hT.symm)

variable [UnivLE.{u, w'}]

section

attribute [local irreducible] effectivePairCohomology

set_option maxHeartbeats 750000 in
-- The two weakening maps agree on the original pair with empty smaller support.
/-- Weakening the bounds of a window commutes with the original stage maps. -/
theorem coniveauCohomologyToWindow_comp_windowMap (K : DM(k)) (n : ℤ)
    {a b a' b' : ℕ} (ha : a' ≤ a) (hb : b' ≤ b) :
    coniveauCohomologyToWindow k X K n a b ≫ coniveauWindowMap k X K n ha hb =
      coniveauCohomologyTransition k X K n ha ≫ coniveauCohomologyToWindow k X K n a' b' := by
  apply colimit.hom_ext
  intro W
  let T := coniveauEmptySupportPair k X (b := b) W
  let T' := (coniveauSupportPairsWeaken k X ha hb).obj T
  let R := coniveauCohomologyToWindow k X K n a b
  let R' := coniveauCohomologyToWindow k X K n a' b'
  let S := coniveauCohomologyTransition k X K n ha
  let M := coniveauWindowMap k X K n ha hb
  let i := colimit.ι (coniveauCohomologyDiagram k X K n a) T.1.2
  let i' := colimit.ι (coniveauCohomologyDiagram k X K n a') T'.1.2
  let j := colimit.ι (coniveauRelativeSupportDiagram k X K n a b) T
  let j' := colimit.ι (coniveauRelativeSupportDiagram k X K n a' b') T'
  let ρ := (coniveauRelativeSupportRestriction k X K n a b).app T
  let ρ' := (coniveauRelativeSupportRestriction k X K n a' b').app T'
  have hR : i ≫ R = ρ ≫ j := ι_coniveauCohomologyToWindow k X K n T
  have hR' : i' ≫ R' = ρ' ≫ j' := ι_coniveauCohomologyToWindow k X K n T'
  have hS : i ≫ S = i' := ι_coniveauCohomologyTransition k X K n ha T.1.2
  have hM : j ≫ M = j' := ι_coniveauWindowMap k X K n ha hb T
  have hArrow : supportPairFirstArrow k X T = supportPairFirstArrow k X T' := by
    apply Arrow.hom_ext <;> rfl
  have hρ : ρ = ρ' :=
    (effectivePairCohomology k K n).congr_map (congrArg Quiver.Hom.op hArrow)
  change i ≫ R ≫ M = i ≫ S ≫ R'
  exact generator_square i i' j j' R R' S M ρ ρ' hR hR' hS hM hρ

end

set_option maxHeartbeats 750000 in
-- Exactness is applied at the stage and window with zero adjacent stages.
/-- Past the dimension bound, the original stage-to-window map is an isomorphism. -/
theorem isIso_coniveauCohomologyToWindow_above_dimension (K : DM(k)) (n : ℤ)
    {a b d : ℕ} (hab : a ≤ b) (hX : topologicalKrullDim X.left ≤ d) (hdb : d < b) :
    IsIso (coniveauCohomologyToWindow k X K n a b) := by
  have h₀ := isZero_coniveauCohomology_above_dimension k X K n hX hdb
  have h₁ := isZero_coniveauCohomology_above_dimension k X K (n + 1) hX hdb
  let : Mono (coniveauCohomologyToWindow k X K n a b) :=
    (coniveauCohomologyStage_exact k X K n hab).mono_g (h₀.eq_of_src _ _)
  let : Epi (coniveauCohomologyToWindow k X K n a b) :=
    (coniveauCohomologyWindow_exact k X K n hab).epi_f (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- A window extending beyond the dimension bound is the original coniveau stage. -/
@[no_expose]
def coniveauAbsoluteWindowIso (K : DM(k)) (n : ℤ)
    {a b d : ℕ} (hab : a ≤ b) (hX : topologicalKrullDim X.left ≤ d) (hdb : d < b) :
    coniveauCohomology k X K n a ≅ coniveauRelativeSupportCohomology k X K n a b := by
  let := isIso_coniveauCohomologyToWindow_above_dimension k X K n hab hX hdb
  exact asIso (coniveauCohomologyToWindow k X K n a b)

/-- The finite window comparison retains the original stage-to-window map. -/
theorem coniveauAbsoluteWindowIso_hom (K : DM(k)) (n : ℤ)
    {a b d : ℕ} (hab : a ≤ b) (hX : topologicalKrullDim X.left ≤ d) (hdb : d < b) :
    (coniveauAbsoluteWindowIso k X K n hab hX hdb).hom =
      coniveauCohomologyToWindow k X K n a b := by
  unfold coniveauAbsoluteWindowIso
  rfl

set_option maxHeartbeats 750000 in
-- Each generator maps to the pair with both supports equal to its larger support.
/-- A diagonal coniveau window vanishes. -/
theorem isZero_coniveauRelativeSupportCohomology_self (K : DM(k)) (n : ℤ) (a : ℕ) :
    IsZero (coniveauRelativeSupportCohomology k X K n a a) := by
  let F := coniveauRelativeSupportDiagram k X K n a a
  apply (IsZero.iff_id_eq_zero _).2
  apply colimit.hom_ext
  intro T
  let W := T.1.2
  let S : ConiveauSupportPairs k X a a := ⟨(W, W), le_rfl⟩
  let f : T ⟶ S := homOfLE (show T.1 ≤ (W, W) from ⟨T.2, le_rfl⟩)
  have hS : IsZero (F.obj S) :=
    isZero_relativeOpenPairCohomology_refl k X K n W.1.compl
  have hι : colimit.ι F S = 0 := hS.eq_of_src _ _
  have hT : colimit.ι F T = 0 := (colimit.w F f).symm.trans (by rw [hι, comp_zero])
  change colimit.ι F T ≫ 𝟙 _ = colimit.ι F T ≫ 0
  rw [Category.comp_id, comp_zero, hT]

end AlgebraicGeometry.MotivicHomotopy

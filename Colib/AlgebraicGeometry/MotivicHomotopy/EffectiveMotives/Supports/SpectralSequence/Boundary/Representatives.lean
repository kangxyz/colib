/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.AbsoluteWindows
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.ClosedSupports
import all Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Basic

/-!
# Agreement of the coniveau boundaries on a flag

On a flag of closed supports starting with the empty support, the spectral
object boundary is the original localization boundary into the middle support,
followed by its restriction to the relative pair.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme Opposite TopologicalSpace
open scoped CategoryTheory.Pretriangulated.Opposite

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))
local notation "DM(" field ")" => EffectiveMotivesMinus field

variable (X : Sm(k))
  [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The transfer-sheaf abelian structure used in comparing flag boundaries. -/
local instance coniveauBoundaryRepresentativesAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

private theorem postcompose_boundary {C : Type*} [Category* C] {A B D E : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ D} (h : a ≫ b = c) (v : D ⟶ E) :
    c ≫ v = a ≫ b ≫ v :=
  (congrArg (· ≫ v) h.symm).trans (Category.assoc _ _ _)

private theorem boundary_change_of_identity {C A : Type*} [Category* C] [Category* A]
    [HasShift C ℤ] (F : A ⥤ C) {P B B' : A}
    (a : P ⟶ P) (e : B ⟶ B') (ha : a = 𝟙 P)
    (b : F.obj B ⟶ (F.obj P)⟦(1 : ℤ)⟧) (b' : F.obj B' ⟶ (F.obj P)⟦(1 : ℤ)⟧)
    (h : F.map e ≫ b' = b ≫ (F.map a)⟦(1 : ℤ)⟧') :
    F.map e ≫ b' = b := by
  let S := shiftFunctor C (1 : ℤ)
  have hF : F.map a = 𝟙 _ := (F.congr_map ha).trans (F.map_id _)
  have hS : S.map (F.map a) = 𝟙 _ := (S.congr_map hF).trans (S.map_id _)
  exact h.trans ((congrArg (b ≫ ·) hS).trans (Category.comp_id _))

private theorem boundary_eq_of_formulas {C : Type*} [Category* C] [Preadditive C]
    (A : AddCommGrpCat) {B B' D E : C} (e : B ⟶ B')
    (b : B ⟶ D) (b' : B' ⟶ D) (h : e ≫ b' = b)
    (r : AddCommGrpCat.of (B' ⟶ E) ⟶ AddCommGrpCat.of (B ⟶ E))
    (s : A ⟶ AddCommGrpCat.of (B ⟶ E)) (s' : A ⟶ AddCommGrpCat.of (B' ⟶ E))
    (v : A → (D ⟶ E))
    (hs : ∀ x, s x = b ≫ v x) (hs' : ∀ x, s' x = b' ≫ v x)
    (hr : ∀ x, r x = e ≫ x) :
    s = s' ≫ r := by
  apply ConcreteCategory.hom_ext
  intro x
  change s x = r (s' x)
  exact (hs x).trans ((postcompose_boundary h (v x)).trans
    ((congrArg (e ≫ ·) (hs' x).symm).trans (hr (s' x)).symm))

set_option maxHeartbeats 650000 in
-- The map of nested opens is the identity on the first two opens.
private theorem nestedPairBoundary_change_ambient {U V W Y : Sm(k)}
    (i : U ⟶ V) (j : V ⟶ W) (j' : V ⟶ Y) (e : W ⟶ Y)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (h : j ≫ e = 𝟙 V ≫ j') :
    (effectivePairMotiveFunctor k).map (Arrow.homMk' (𝟙 V) e h.symm) ≫
        effectiveNestedPairBoundary k i j' = effectiveNestedPairBoundary k i j := by
  let F := effectivePairMotiveFunctor k
  have hi : i ≫ 𝟙 V = 𝟙 U ≫ i :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  let α : Arrow.mk i ⟶ Arrow.mk i := Arrow.homMk' (𝟙 U) (𝟙 V) hi.symm
  let ρ : Arrow.mk j ⟶ Arrow.mk j' := Arrow.homMk' (𝟙 V) e h.symm
  have hα : α = 𝟙 _ := by
    apply Arrow.hom_ext <;> rfl
  exact boundary_change_of_identity F α ρ hα
    (effectiveNestedPairBoundary k i j) (effectiveNestedPairBoundary k i j')
    (effectiveNestedPairBoundary_naturality k i j i j' (𝟙 U) (𝟙 V) e hi h)

set_option maxHeartbeats 650000 in
-- The spectral object and the relative diagrams evaluate the same complementary opens.
/-- The signed spectral boundary on a flag obtained by placing the empty support first. -/
def coniveauEmptyFlagBoundary (K : DM(k)) (n : ℤ) {a b c : ℕ}
    (ZW : ConiveauSupportPairs k X a b) :
    (coniveauRelativeSupportDiagram k X K n a b).obj ZW ⟶
      (coniveauRelativeSupportDiagram k X K (n + 1) b c).obj
        (coniveauEmptySupportPair k X (b := c) ZW.1.1) :=
  (closedSupportSpectralObject k X K).δ
    (homOfLE (bot_le : (⊥ : Closeds X.left) ≤ ZW.1.1.1)) (homOfLE ZW.2) n (n + 1) rfl

set_option maxHeartbeats 900000 in
-- Compare the published signed formulas on each represented cohomology class.
/-- The connecting map on a flag starting at the empty support agrees with the original
absolute nested-pair boundary followed by the empty-support comparison. -/
theorem closedSupportSpectralObject_δ_bot (K : DM(k)) (n : ℤ) {a b c : ℕ}
    (ZW : ConiveauSupportPairs k X a b) :
    let β : (coniveauRelativeSupportDiagram k X K n a b).obj ZW ⟶
        (coniveauCohomologyDiagram k X K (n + 1) b).obj ZW.1.1 :=
      (coniveauRelativeSupportBoundary k X K n a b).app ZW
    let ρ : (coniveauCohomologyDiagram k X K (n + 1) b).obj ZW.1.1 ⟶
        (coniveauRelativeSupportDiagram k X K (n + 1) b c).obj
          (coniveauEmptySupportPair k X (b := c) ZW.1.1) :=
      (coniveauRelativeSupportRestriction k X K (n + 1) b c).app
        (coniveauEmptySupportPair k X (b := c) ZW.1.1)
    coniveauEmptyFlagBoundary k X K n (c := c) ZW = β ≫ ρ := by
  let i := supportOpenMap k X ZW.2
  let h : (⊥ : Closeds X.left) ≤ ZW.1.1.1 := bot_le
  let j := supportOpenMap k X h
  let j' := supportOpenInclusion k X ZW.1.1.1
  let e := supportOpenInclusion k X (⊥ : Closeds X.left)
  let F := effectivePairMotiveFunctor k
  let A := coniveauEmptySupportPair k X (b := c) ZW.1.1
  let ρ := supportPairFirstArrow k X A
  let δ := effectiveNestedPairBoundary k i j
  let δ' := effectiveNestedPairBoundary k i j'
  have he : j ≫ e = 𝟙 _ ≫ j' :=
    (supportOpenMap_comp_inclusion k X h).trans (Category.id_comp _).symm
  have hδ : F.map ρ ≫ δ' = δ := nestedPairBoundary_change_ambient k i j j' e he
  let norm := (closedSupportSpectralObject k X K).δ (homOfLE h) (homOfLE ZW.2)
    n (n + 1) rfl
  let original := (coniveauRelativeSupportBoundary k X K n a b).app ZW
  let r := (coniveauRelativeSupportRestriction k X K (n + 1) b c).app A
  let v (x : effectivePairMotive k i ⟶ K⟦n⟧) :=
    x⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' DM(k) n 1 (n + 1) rfl).inv.app K
  change norm = original ≫ r
  exact boundary_eq_of_formulas _ (F.map ρ) δ δ' hδ r norm original v
    (closedSupportSpectralObject_δ_apply k X K n (n + 1) rfl h ZW.2)
    (coniveauRelativeSupportBoundary_app_apply k X K n ZW) (fun _ ↦ rfl)

end AlgebraicGeometry.MotivicHomotopy

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.A1Prespectrum
import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Collapse
import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.NisnevichFibrantReplacement
import Colib.CategoryTheory.Sites.Simplicial.IntervalFibrantReplacement
import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalHom
import Colib.CategoryTheory.Sites.Simplicial.StalkwiseFibrantHom

/-!
# Strict realization of motivic Tate prespectra

Choose a local fibrant model in each degree. The original Hom comparison
lifts each given Tate bonding map to the actual smash of pointed simplicial
presheaves. The resulting level isomorphisms identify the localized
prespectrum with the given one, including its bonding maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)
local notation "Iᵣ" => affineLineInterval (Spec R)
local notation "Qₛ" => toStalkwiseHomotopyCategory Cᵣ Jᵣ
local notation "Qᵢ" => toAffineLineHomotopyCategory (Spec R)
local notation "P" => tatePresheafSuspension R
local notation "T" => motivicTateSuspension R

private theorem intervalLocal_of_iso
    {A B : StalkwiseHomotopyCategory.{u + 1} Cᵣ Jᵣ} (e : A ≅ B)
    (h : IsIntervalLocal Cᵣ Jᵣ Iᵣ A) :
    IsIntervalLocal Cᵣ Jᵣ Iᵣ B := by
  intro X
  let q := (Qₛ).map (cylinderProjection X Iᵣ)
  let e₁ : ((Qₛ).obj X ⟶ A) ≃ ((Qₛ).obj X ⟶ B) := e.homToEquiv
  let e₂ : ((Qₛ).obj (parameterizedCylinder X Iᵣ) ⟶ A) ≃
      ((Qₛ).obj (parameterizedCylinder X Iᵣ) ⟶ B) := e.homToEquiv
  let f := fun a : (Qₛ).obj X ⟶ A ↦ q ≫ a
  have he : (fun b : (Qₛ).obj X ⟶ B ↦ q ≫ b) = e₂ ∘ f ∘ e₁.symm := by
    funext b
    change q ≫ b = (q ≫ b ≫ e.inv) ≫ e.hom
    rw [Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]
  change Function.Bijective (fun b : (Qₛ).obj X ⟶ B ↦ q ≫ b)
  rw [he]
  exact e₂.bijective.comp ((h X).comp e₁.symm.bijective)

private theorem exists_strictLocalModel (X : AffineLineHomotopyCategory (Spec R)) :
    ∃ Y : PointedSimplicialPresheaf.{u + 1} Cᵣ,
      IsStalkwiseInjectiveFibrant Cᵣ Jᵣ Y ∧ IsIntervalLocal Cᵣ Jᵣ Iᵣ ((Qₛ).obj Y) ∧
        Nonempty ((Qᵢ).obj Y ≅ X) := by
  let A := (Qᵢ).objPreimage X
  obtain ⟨B, f, hf, hB⟩ := exists_intervalLocalFibrantReplacement Cᵣ Jᵣ
    (affineLineParameterEndpoint R 0) A
  obtain ⟨Y, g, hg, hY⟩ := exists_nisnevichInjectiveFibrantReplacement R B
  have h₁ : IsIso ((Qᵢ).map f) := (intervalWeakEquivalences Cᵣ Jᵣ Iᵣ).Q_inverts f hf
  have h₂ : IsIso ((Qₛ).map g) := isIso_toStalkwiseHomotopyCategory_map Cᵣ g hg.2
  have h₃ : IsIso ((Qᵢ).map g) := (intervalWeakEquivalences Cᵣ Jᵣ Iᵣ).Q_inverts g
    (stalkwiseWeakEquivalences_le_intervalWeakEquivalences Cᵣ Jᵣ Iᵣ g hg.2)
  let e := @asIso _ _ _ _ ((Qₛ).map g) h₂
  let e₁ := @asIso _ _ _ _ ((Qᵢ).map f) h₁
  let e₂ := @asIso _ _ _ _ ((Qᵢ).map g) h₃
  exact ⟨Y, hY, intervalLocal_of_iso R e hB,
    ⟨e₂.symm ≪≫ e₁.symm ≪≫ (Qᵢ).objObjPreimageIso X⟩⟩

private theorem surjective_motivicMap_of_localFibrant
    (X Y : PointedSimplicialPresheaf.{u + 1} Cᵣ)
    (hY : IsStalkwiseInjectiveFibrant Cᵣ Jᵣ Y)
    (hL : IsIntervalLocal Cᵣ Jᵣ Iᵣ ((Qₛ).obj Y)) :
    Function.Surjective (fun f : X ⟶ Y ↦ (Qᵢ).map f) := by
  intro g
  let e := intervalLocalHomEquiv Cᵣ Jᵣ Iᵣ Y hL X
  obtain ⟨f, hf⟩ := surjective_stalkwise_map_of_isStalkwiseInjectiveFibrant Jᵣ hY X (e g)
  exact ⟨f, e.injective ((intervalLocalHomEquiv_map Cᵣ Jᵣ Iᵣ Y hL X f).trans hf)⟩

variable (E : A1TatePrespectrum R)

private def realizationLevel (n : ℕ) : PointedSimplicialPresheaf.{u + 1} Cᵣ :=
  (exists_strictLocalModel R (E.level n)).choose

private theorem realizationLevel_isFibrant (n : ℕ) :
    IsStalkwiseInjectiveFibrant Cᵣ Jᵣ (realizationLevel R E n) :=
  (exists_strictLocalModel R (E.level n)).choose_spec.1

private theorem realizationLevel_isLocal (n : ℕ) :
    IsIntervalLocal Cᵣ Jᵣ Iᵣ ((Qₛ).obj (realizationLevel R E n)) :=
  (exists_strictLocalModel R (E.level n)).choose_spec.2.1

private def realizationLevelIso (n : ℕ) :
    (Qᵢ).obj (realizationLevel R E n) ≅ E.level n :=
  (exists_strictLocalModel R (E.level n)).choose_spec.2.2.some

private def realizationBondingImage (n : ℕ) :
    (Qᵢ).obj ((P).obj (realizationLevel R E n)) ⟶
      (Qᵢ).obj (realizationLevel R E (n + 1)) :=
  (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).inv.app
      (realizationLevel R E n) ≫
    (T).map (realizationLevelIso R E n).hom ≫ E.bonding n ≫
    (realizationLevelIso R E (n + 1)).inv

private theorem exists_realizationBonding (n : ℕ) :
    ∃ f : (P).obj (realizationLevel R E n) ⟶ realizationLevel R E (n + 1),
      (Qᵢ).map f = realizationBondingImage R E n :=
  surjective_motivicMap_of_localFibrant R _ _ (realizationLevel_isFibrant R E (n + 1))
    (realizationLevel_isLocal R E (n + 1)) (realizationBondingImage R E n)

/-- A strict Tate prespectrum realizing the given prespectrum in A¹-homotopy. -/
@[no_expose]
def strictTateRealization : TatePrespectrum R where
  level := realizationLevel R E
  bonding n := (exists_realizationBonding R E n).choose

/-- The chosen strict realization is Nisnevich-injective fibrant in every degree. -/
theorem strictTateRealization_level_isFibrant (n : ℕ) :
    IsStalkwiseInjectiveFibrant Cᵣ Jᵣ ((strictTateRealization R E).level n) := by
  unfold strictTateRealization
  exact realizationLevel_isFibrant R E n

/-- Every degree of the strict realization is A¹-local in Nisnevich homotopy. -/
theorem strictTateRealization_level_isLocal (n : ℕ) :
    IsIntervalLocal Cᵣ Jᵣ Iᵣ ((Qₛ).obj ((strictTateRealization R E).level n)) := by
  unfold strictTateRealization
  exact realizationLevel_isLocal R E n

/-- The strict realization recovers the original prespectrum with its actual bonding maps. -/
@[no_expose]
def strictTateRealizationIso : ((toA1TatePrespectrum R).obj (strictTateRealization R E)) ≅ E := by
  let X := (toA1TatePrespectrum R).obj (strictTateRealization R E)
  let e (n : ℕ) : X.level n ≅ E.level n := realizationLevelIso R E n
  have h (n : ℕ) : X.bonding n ≫ (e (n + 1)).hom = (T).map (e n).hom ≫ E.bonding n := by
    let a := (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).app
      (realizationLevel R E n)
    let f := (exists_realizationBonding R E n).choose
    have hf : (Qᵢ).map f = realizationBondingImage R E n :=
      (exists_realizationBonding R E n).choose_spec
    change (a.hom ≫ (Qᵢ).map f) ≫ (e (n + 1)).hom = _
    rw [hf]
    unfold realizationBondingImage
    change (a.hom ≫ (a.inv ≫ (T).map (e n).hom ≫ E.bonding n ≫ (e (n + 1)).inv)) ≫
      (e (n + 1)).hom = _
    calc
      _ = (((T).map (e n).hom ≫ E.bonding n) ≫ (e (n + 1)).inv) ≫
          (e (n + 1)).hom := by
        simp only [a.hom_inv_id_assoc, Category.assoc]
      _ = _ := (Category.assoc _ _ _).trans
        ((congrArg (((T).map (e n).hom ≫ E.bonding n) ≫ ·) (e (n + 1)).inv_hom_id).trans
          (Category.comp_id _))
  refine ⟨⟨fun n ↦ (e n).hom, h⟩, ⟨fun n ↦ (e n).inv, ?_⟩, ?_, ?_⟩
  · intro n
    apply (cancel_mono (e (n + 1)).hom).1
    change (E.bonding n ≫ (e (n + 1)).inv) ≫ (e (n + 1)).hom =
      ((T).map (e n).inv ≫ X.bonding n) ≫ (e (n + 1)).hom
    calc
      _ = E.bonding n := (Category.assoc _ _ _).trans
        ((congrArg (E.bonding n ≫ ·) (e (n + 1)).inv_hom_id).trans (Category.comp_id _))
      _ = (T).map ((e n).inv ≫ (e n).hom) ≫ E.bonding n := by
        rw [(e n).inv_hom_id, (T).map_id, Category.id_comp]
      _ = (T).map (e n).inv ≫ ((T).map (e n).hom ≫ E.bonding n) :=
        (T).map_comp_assoc _ _ _
      _ = (T).map (e n).inv ≫ (X.bonding n ≫ (e (n + 1)).hom) :=
        congrArg ((T).map (e n).inv ≫ ·) (h n).symm
      _ = _ := (Category.assoc _ _ _).symm
  · exact SequentialPrespectrum.Hom.ext (funext fun n ↦ (e n).hom_inv_id)
  · exact SequentialPrespectrum.Hom.ext (funext fun n ↦ (e n).inv_hom_id)

end AlgebraicGeometry.MotivicHomotopy

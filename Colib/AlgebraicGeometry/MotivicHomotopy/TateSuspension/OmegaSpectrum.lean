/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.MotivicAdjunction
public import Colib.CategoryTheory.Prespectrum.StableComparison
import Colib.CategoryTheory.Sites.Simplicial.StalkwiseInitial
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The Tate Ω-spectrum condition

For the specified motivic Tate adjunction, the Ω-spectrum condition is
tested by the original free prespectrum comparisons in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)

instance : HasInitial (AffineLineHomotopyCategory (Spec R)) := by
  let Q := stalkwiseToIntervalHomotopyCategory Cᵣ Jᵣ (affineLineInterval (Spec R))
  let : Q.IsLeftAdjoint := (motivicLocalizationAdjunction R).isLeftAdjoint
  let X := (toStalkwiseHomotopyCategory.{u + 1} Cᵣ Jᵣ).obj (point.{u + 1} Cᵣ)
  have hX : IsInitial X := isInitial_stalkwisePoint.{u + 1} Jᵣ
    (exists_nisnevichInjectiveFibrantReplacement R)
  exact (hX.isInitialObj Q X).hasInitial

instance : (motivicTateSuspension R).IsLeftAdjoint :=
  (motivicTateAdjunction R).isLeftAdjoint

/-- The Ω-spectra for the original Tate suspension and its motivic right adjoint. -/
abbrev MotivicTateOmegaSpectrum := SequentialPrespectrum.OmegaSpectrum (motivicTateAdjunction R)

/-- The Ω-spectrum condition is exactly the Hom test against the original
free prespectrum comparisons. -/
theorem isOmegaSpectrum_iff_bijective_precomp_tateComparison (Y : A1TatePrespectrum R) :
    SequentialPrespectrum.IsOmegaSpectrum (motivicTateAdjunction R) Y ↔
      ∀ (n : ℕ) (X : AffineLineHomotopyCategory (Spec R)),
        Function.Bijective
          (fun f : (SequentialPrespectrum.freeAt (S := motivicTateSuspension R) n).obj X ⟶ Y ↦
            SequentialPrespectrum.freeAtSuccComparison n X ≫ f) :=
  SequentialPrespectrum.isOmegaSpectrum_iff_bijective_precomp_freeAtSuccComparison
    (motivicTateAdjunction R) Y

/-- It suffices to test the Tate bonding maps on the actual images of
pointed simplicial presheaves in the A¹-localization. -/
theorem isOmegaSpectrum_of_bijective_bonding (Y : A1TatePrespectrum R)
    (h : ∀ (n : ℕ) (X : PointedSimplicialPresheaf.{u + 1} Cᵣ), Function.Bijective
      (fun f : (toAffineLineHomotopyCategory (Spec R)).obj X ⟶ Y.level n ↦
        (motivicTateSuspension R).map f ≫ Y.bonding n)) :
    SequentialPrespectrum.IsOmegaSpectrum (motivicTateAdjunction R) Y := by
  apply (SequentialPrespectrum.isOmegaSpectrum_iff_bijective_bonding
    (motivicTateAdjunction R) Y).2
  intro n A
  let Q := toAffineLineHomotopyCategory (Spec R)
  let F := motivicTateSuspension R
  let e := Q.objObjPreimageIso A
  let a : (A ⟶ Y.level n) ≃ (Q.obj (Q.objPreimage A) ⟶ Y.level n) := e.symm.homFromEquiv
  let b : (F.obj A ⟶ Y.level (n + 1)) ≃
      (F.obj (Q.obj (Q.objPreimage A)) ⟶ Y.level (n + 1)) := (F.mapIso e).symm.homFromEquiv
  let p := fun f : A ⟶ Y.level n ↦ F.map f ≫ Y.bonding n
  let q := fun f : Q.obj (Q.objPreimage A) ⟶ Y.level n ↦ F.map f ≫ Y.bonding n
  have hp : b ∘ p = q ∘ a := by
    funext f
    change F.map e.hom ≫ F.map f ≫ Y.bonding n = F.map (e.hom ≫ f) ≫ Y.bonding n
    rw [F.map_comp, Category.assoc]
  apply (Function.Bijective.of_comp_iff' b.bijective p).1
  rw [hp]
  exact (h n (Q.objPreimage A)).comp a.bijective

end AlgebraicGeometry.MotivicHomotopy

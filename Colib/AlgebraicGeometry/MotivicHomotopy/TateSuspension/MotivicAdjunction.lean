/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.A1Prespectrum
public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalizedAdjunction
import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Collapse
import Colib.CategoryTheory.Sites.Simplicial.IntervalFibrantReplacement

/-!
# The motivic Tate suspension adjunction

The actual Nisnevich Tate loop functor preserves A¹-local objects.
A¹-local replacement and the cylinder comparison give the adjunction
for the suspension of the original motivic prespectrum.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)
local notation "Iᵣ" => affineLineInterval (Spec R)
local notation "Qₛ" => toStalkwiseHomotopyCategory Cᵣ Jᵣ
local notation "Qᵢ" => toAffineLineHomotopyCategory (Spec R)
local notation "L" => stalkwiseToIntervalHomotopyCategory Cᵣ Jᵣ Iᵣ

/-- An object in the chosen A¹-localization admits a model whose stalkwise
image is already A¹-local. -/
theorem exists_motivicLocalModel (Y : AffineLineHomotopyCategory (Spec R)) :
    ∃ X : StalkwiseHomotopyCategory.{u + 1} Cᵣ Jᵣ,
      IsIntervalLocal Cᵣ Jᵣ Iᵣ X ∧ Nonempty ((L).obj X ≅ Y) := by
  let X := (Qᵢ).objPreimage Y
  obtain ⟨Z, f, hf, hZ⟩ := exists_intervalLocalFibrantReplacement Cᵣ Jᵣ
    (affineLineParameterEndpoint R 0) X
  have hi : IsIso ((Qᵢ).map f) := (intervalWeakEquivalences Cᵣ Jᵣ Iᵣ).Q_inverts f hf
  exact ⟨(Qₛ).obj Z, hZ, ⟨(stalkwiseToIntervalHomotopyCategoryCompIso Cᵣ Jᵣ Iᵣ).app Z ≪≫
    (@asIso _ _ _ _ ((Qᵢ).map f) hi).symm ≪≫ (Qᵢ).objObjPreimageIso Y⟩⟩

/-- The functor from Nisnevich homotopy to motivic homotopy is a reflection. -/
@[no_expose]
def motivicLocalizationAdjunction :
    (L) ⊣ intervalLocalInclusion Jᵣ Iᵣ (exists_motivicLocalModel R) :=
  intervalReflectorAdjunction Jᵣ Iᵣ (exists_motivicLocalModel R)

private def motivicTateSuspensionComparison :
    (L) ⋙ motivicTateSuspension R ≅ tateStalkwiseSuspension R ⋙ (L) := by
  let α := stalkwiseToIntervalHomotopyCategoryCompIso Cᵣ Jᵣ Iᵣ
  let β := tateStalkwiseSuspensionCompIso R
  let W := stalkwiseWeakEquivalences.{u + 1} Cᵣ Jᵣ
  let H := Localization.fullyFaithfulWhiskeringLeft (Qₛ) W
    (AffineLineHomotopyCategory (Spec R))
  apply H.preimageIso
  calc
    _ ≅ ((Qₛ) ⋙ (L)) ⋙ motivicTateSuspension R := (Functor.associator _ _ _).symm
    _ ≅ (Qᵢ) ⋙ motivicTateSuspension R := isoWhiskerRight α _
    _ ≅ tatePresheafSuspension R ⋙ (Qᵢ) :=
      tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)
    _ ≅ tatePresheafSuspension R ⋙ ((Qₛ) ⋙ (L)) := isoWhiskerLeft _ α.symm
    _ ≅ (tatePresheafSuspension R ⋙ (Qₛ)) ⋙ (L) := (Functor.associator _ _ _).symm
    _ ≅ ((Qₛ) ⋙ tateStalkwiseSuspension R) ⋙ (L) := isoWhiskerRight β.symm _
    _ ≅ _ := Functor.associator _ _ _

/-- The motivic Tate loop functor uses the original pointed internal Hom on
an A¹-local fibrant representative. -/
@[no_expose]
def motivicTateLoops : AffineLineHomotopyCategory (Spec R) ⥤ AffineLineHomotopyCategory (Spec R) :=
  (intervalLocalInclusion Jᵣ Iᵣ (exists_motivicLocalModel R) ⋙ tateStalkwiseLoops R) ⋙ (L)

/-- The actual Tate suspension and Tate loops on the motivic homotopy category. -/
@[no_expose]
def motivicTateAdjunction : motivicTateSuspension R ⊣ motivicTateLoops R :=
  intervalLocalizedAdjunction Jᵣ Iᵣ (exists_motivicLocalModel R) (tateStalkwiseAdjunction R)
    (motivicTateSuspensionComparison R) (isA1Local_tateRightAdjoint R (tateStalkwiseAdjunction R))

end AlgebraicGeometry.MotivicHomotopy

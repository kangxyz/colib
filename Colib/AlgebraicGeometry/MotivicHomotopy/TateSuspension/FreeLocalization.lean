/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.OmegaSpectrum
public import Colib.CategoryTheory.Prespectrum.FreeComparison
public import Mathlib.CategoryTheory.Adjunction.Limits
import Colib.CategoryTheory.Sites.Simplicial.StalkwiseInitial

/-!
# Localizing a free Tate prespectrum

The levelwise localization carries the actual strict free Tate
prespectrum to the free prespectrum on the localized generator.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)
local notation "Q" => toAffineLineHomotopyCategory (Spec R)

local instance : (tatePresheafSuspension R).IsLeftAdjoint :=
  (tatePresheafAdjunction R).isLeftAdjoint

private theorem preservesInitial_toAffineLineHomotopyCategory :
    PreservesColimit (Functor.empty.{0} (PointedSimplicialPresheaf.{u + 1} Cᵣ)) (Q) := by
  let L := stalkwiseToIntervalHomotopyCategory Cᵣ Jᵣ (affineLineInterval (Spec R))
  let Qₛ := toStalkwiseHomotopyCategory.{u + 1} Cᵣ Jᵣ
  let : L.IsLeftAdjoint := (motivicLocalizationAdjunction R).isLeftAdjoint
  let X := point.{u + 1} Cᵣ
  let α := stalkwiseToIntervalHomotopyCategoryCompIso Cᵣ Jᵣ (affineLineInterval (Spec R))
  have hₛ : IsInitial (Qₛ.obj X) :=
    isInitial_stalkwisePoint.{u + 1} Jᵣ (exists_nisnevichInjectiveFibrantReplacement R)
  have h : IsInitial ((Q).obj X) := (hₛ.isInitialObj L _).ofIso (α.app X)
  let e : X ≅ (⊥_ (PointedSimplicialPresheaf.{u + 1} Cᵣ)) :=
    (point_isZero.{u + 1} Cᵣ).isInitial.uniqueUpToIso initialIsInitial
  exact preservesInitial_of_iso (Q) (initialIsInitial.uniqueUpToIso (h.ofIso ((Q).mapIso e)))

local instance : PreservesColimit (Functor.empty.{0} (PointedSimplicialPresheaf.{u + 1} Cᵣ)) (Q) :=
  preservesInitial_toAffineLineHomotopyCategory R

/-- The original levelwise localization commutes with free Tate
prespectra in the specified degree. -/
@[no_expose]
def freeTateAtLocalizationIso (q : ℕ) :
    SequentialPrespectrum.freeAt (S := tatePresheafSuspension R) q ⋙ toA1TatePrespectrum R ≅
      (Q) ⋙ SequentialPrespectrum.freeAt (S := motivicTateSuspension R) q :=
  SequentialPrespectrum.freeAtMapFunctorIso (Q)
    (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)) q

/-- Maps from the localized strict free Tate prespectrum evaluate at
the actual localized generator in the specified degree. -/
@[no_expose]
def localizedFreeTateHomEquiv (q : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cᵣ) (Y : A1TatePrespectrum R) :
    ((toA1TatePrespectrum R).obj
      ((SequentialPrespectrum.freeAt (S := tatePresheafSuspension R) q).obj X) ⟶ Y) ≃
        ((Q).obj X ⟶ Y.level q) :=
  SequentialPrespectrum.freeAtMapHomEquiv (Q)
    (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)) q X Y

/-- Evaluation of a map from the localized strict free Tate prespectrum
retains its original component and generator identification. -/
theorem localizedFreeTateHomEquiv_apply (q : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cᵣ) (Y : A1TatePrespectrum R)
    (f : (toA1TatePrespectrum R).obj
      ((SequentialPrespectrum.freeAt (S := tatePresheafSuspension R) q).obj X) ⟶ Y) :
    localizedFreeTateHomEquiv R q X Y f =
      (Q).map (SequentialPrespectrum.freeAtLevelIso (S := tatePresheafSuspension R) q X).inv ≫
        f.app q :=
  SequentialPrespectrum.freeAtMapHomEquiv_apply (Q)
    (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)) q X Y f

end AlgebraicGeometry.MotivicHomotopy

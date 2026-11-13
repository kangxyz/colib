/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Localization
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Prespectrum
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.StalkwiseAdjunction

/-! # Tate prespectra in the A¹-homotopy category -/

public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

/-- Tate suspension on the A¹-homotopy category, using the actual Nisnevich adjunction. -/
abbrev motivicTateSuspension := tateA1Suspension R (tateStalkwiseAdjunction R)

/-- The sequential prespectra for the actual A¹-localized Tate suspension. -/
abbrev A1TatePrespectrum := SequentialPrespectrum (motivicTateSuspension R)

/-- Localize each original Tate level and bonding map. -/
@[expose]
def toA1TatePrespectrum : TatePrespectrum R ⥤ A1TatePrespectrum R :=
  SequentialPrespectrum.mapFunctor (toAffineLineHomotopyCategory (Spec R))
    (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R))

/-- The level is the image of the original pointed presheaf under localization. -/
theorem toA1TatePrespectrum_obj_level (X : TatePrespectrum R) (n : ℕ) :
    ((toA1TatePrespectrum R).obj X).level n =
      (toAffineLineHomotopyCategory (Spec R)).obj (X.level n) :=
  rfl

/-- The bonding map is the localization of the actual presheaf bonding map,
preceded by the defining Tate suspension comparison. -/
theorem toA1TatePrespectrum_obj_bonding (X : TatePrespectrum R) (n : ℕ) :
    ((toA1TatePrespectrum R).obj X).bonding n =
      (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).hom.app (X.level n) ≫
        (toAffineLineHomotopyCategory (Spec R)).map (X.bonding n) :=
  rfl

end AlgebraicGeometry.MotivicHomotopy

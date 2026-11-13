/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Stalkwise
public import Colib.CategoryTheory.Prespectrum.Basic
import Colib.Util.References

/-!
# Tate prespectra on the smooth site

Use the original right smash with the Tate quotient for the bonding maps.
The Nisnevich localization carries those maps to the corresponding
prespectra for the induced Tate suspension.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

/-- Pointed presheaves with successive bonding maps from their Tate suspensions. -/
@[colib_tag "COL-1115",
  colib_ref "Jardine2000MotivicSpectra" "Section 2, before Section 2.1, p. 464" "adaptation"
  "Sequential bonding maps with the Tate factor on the right in this model"]
abbrev TatePrespectrum := SequentialPrespectrum (tatePresheafSuspension R)

/-- Tate prespectra in the pointed stalkwise homotopy category. -/
@[colib_tag "COL-1115"]
abbrev StalkwiseTatePrespectrum := SequentialPrespectrum (tateStalkwiseSuspension R)

/-- Apply Nisnevich localization to the original levels and bonding maps. -/
@[no_expose, colib_tag "COL-1115"]
def toStalkwiseTatePrespectrum : TatePrespectrum R ⥤ StalkwiseTatePrespectrum R :=
  SequentialPrespectrum.mapFunctor
    (toStalkwiseHomotopyCategory (SmoothSite (Spec R)) (SmoothSite.nisnevichTopology (Spec R)))
    (tateStalkwiseSuspensionCompIso R)

end AlgebraicGeometry.MotivicHomotopy

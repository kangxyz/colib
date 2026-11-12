/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFullRestrictionTelescopeSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFineTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalFullOpenTelescopeSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationTelescopeSquares

/-! # The literal original fine full-open telescope comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The actual comparison retains both original fine full-open quotient maps. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFineRestrictionSquare.lean:27"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem fine_fullRestriction_square :
    Functor.whiskerLeft specUnder (parameterTelescopeRestriction f) ≫
        fineTelescopeComparison P =
      fineTelescopeComparison Q ≫ boundedAboveFlatCoefficientAmbientBassTelescopeOpen f ≫
        boundedAboveFlatCoefficientOpenBassTelescopeRestriction f := by
  dsimp only [fineTelescopeComparison]
  rw [← Category.assoc, fullRestriction_telescope_square]
  simp only [Category.assoc]
  rw [FullOpenTelescope.restriction_square, ← Category.assoc (LocalizationTelescope.openMap f),
    LocalizationTelescope.open_square]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenMaps
public import Colib.KTheory.Waldhausen.GrothendieckGroup.Image


/-! # The raw supported restriction-image grading

The actual quotient retains the original relative restriction image. Only its object grading
and exact zero criterion are selected here. No pair-square pullback or density is assumed.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The unchanged raw supported quotient by the actual relative restriction image. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/ImageQuotientPullback.lean:33"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
abbrev PerfectSupportedOpenImageQuotient :=
  ImageQuotient (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
    (perfectSupportedOpenRestrict_waldhausenExact j T)

/-- Original supported perfect complexes carry their actual relative image-quotient grades. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/ImageQuotientPullback.lean:38"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
def perfectSupportedOpenDeficitGrading :
    Cofinality.Grading (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
      (PerfectSupportedOpenImageQuotient j T) :=
  imageQuotientGrading (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
    (perfectSupportedOpenRestrict_waldhausenExact j T)

/-- The actual supported quotient grade detects exactly the original algebraic image. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/ImageQuotientPullback.lean:45"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
theorem perfectSupportedOpenDeficitGrading_zero_iff
    (K : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) :
    (perfectSupportedOpenDeficitGrading j T).value K = 0 ↔
      objectClass (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) K ∈
        (map (perfectSupportedOpenWeakWaldhausen j T) (perfectSupportedRestrict j T)
          (perfectSupportedOpenRestrict_waldhausenExact j T)).range :=
  imageQuotientGrading_zero_iff _ _ _ K

end AlgebraicGeometry.Scheme.Modules

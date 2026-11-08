/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberSequenceMap

/-! Actual quotient transformation, whole sequence square, inherited cofibration and projection. -/
public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Additivity CategoryTheory.Waldhausen.Fibration
universe u
namespace ColibTest.ScalarCofiberSequenceMap
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The whole quotient transformation remains the exact old whiskered zero-to-inclusion. -/
theorem original_quotient_transformation :
    perfectOpenScalarZeroToCone j r q hq =
      Functor.whiskerLeft (perfectOpenScalarConeFunctor j r q hq)
        (zeroToAcyclicInclusion (perfectOpenNested j)) := rfl

/-- The entire natural square retains both chosen-zero and signed-cone arrows. -/
theorem original_quotient_square :
    QuotientRows.oneIdToZero (perfectOpenNested j).coarse ≫
        perfectOpenScalarZeroToCone j r q hq =
      perfectScalarInclusionNat X r ≫ perfectScalarConeProjectionNat X r :=
  perfectOpenScalarZeroToCone_sequence j r q hq

/-- Every inherited source cofibration retains the original relative pushout comparison. -/
theorem original_inherited_cofibration {K L : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))} (g : K ⟶ L)
    (hg : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof g) :
    (perfectOpenNested j).coarse.cof
      (comparison (perfectOpenNested j).coarse (perfectScalarInclusionNat X r)
        (perfectOpenScalarCofibrationSequence j r).cofibration.app_cof (Arrow.mk g)) :=
  (perfectOpenScalarCofibrationSequence j r).cofibration.relative_cof g hg

/-- The same original projection is already fine weak and composes to the entire original scalar. -/
theorem original_projection_and_scalar (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq ((perfectScalarProjectionNat X
      r).app K) ∧
      perfectScalarInclusionNat X r ≫ perfectScalarProjectionNat X r = perfectGlobalScalar X r :=
  ⟨perfectScalarProjectionNat_weak X r K, perfectScalarInclusionNat_projection X r⟩

end ColibTest.ScalarCofiberSequenceMap

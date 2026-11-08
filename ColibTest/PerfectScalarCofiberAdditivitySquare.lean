/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberAdditivitySquare

/-! # The literal scalar square, four whole original faces and both independent zero times -/
set_option warningAsError true
set_option autoImplicit false
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
    CategoryTheory.Waldhausen.Fibration
open SSet
open scoped Simplicial Topology
universe u
namespace ColibTest.ScalarCofiberAdditivitySquare
local instance (X : Scheme.{u}) : HasBinaryCoproducts (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The exact old generic construction is visible at the literal sequence map. -/
theorem original_sequence_specialization :
    perfectOpenScalarBasedAdditivitySquare j r q hq =
      subdividedBasedAdditivityTransformationSquare (RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace) (perfectOpenNested
        j).coarse
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) :=
  perfectOpenScalarBasedAdditivitySquare_eq j r q hq

/-- The complete identity-sequence additivity path remains present. -/
theorem original_identity_face (s : unitInterval) (x : |SSet.diagonalSSet
  (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (0, (s, x)) =
      subdividedBasedAdditivityHomotopy (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenNested j).coarse
        (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
          X.toRingedSpace))))) (QuotientRows.oneIdToZero (perfectOpenNested j).coarse)
        (perfectOpenScalarIdentityCofibrationSequence j) (s, x) :=
  perfectOpenScalarBasedAdditivitySquare_transformation_zero j r q hq s x

/-- The complete original signed-cone sequence additivity path remains present. -/
theorem original_scalar_face (s : unitInterval) (x : |SSet.diagonalSSet
  (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (1, (s, x)) =
      subdividedBasedAdditivityHomotopy (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenNested j).coarse
        (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
        (perfectOpenScalarCofibrationSequence j r) (s, x) :=
  perfectOpenScalarBasedAdditivitySquare_transformation_one j r q hq s x

/-- The whole inclusion edge uses the actual first-half restriction. -/
theorem original_inclusion_face (t : unitInterval) (x : |SSet.diagonalSSet
  (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (t, (0, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarInclusionDiagonalHomotopy j r q hq)
        (t, (realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet
          (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))) x) :=
  perfectOpenScalarBasedAdditivitySquare_additivity_zero j r q hq t x

/-- The whole quotient-first edge keeps the other half and the same normalized sum cylinder. -/
theorem original_sum_face (t : unitInterval) (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙
  bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (t, (1, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarSumDiagonalHomotopy j r q hq) (t, x) :=
  perfectOpenScalarBasedAdditivitySquare_additivity_one j r q hq t x

/-- Both independent continuous times fix the original subdivided zero. -/
theorem original_full_zero (t s : unitInterval) :
    perfectOpenScalarBasedAdditivitySquare j r q hq
      (t, (s, subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))) =
        realizationPoint (diagonalZeroVertex (perfectOpenNested j).coarse) :=
  perfectOpenScalarBasedAdditivitySquare_fixed_zero j r q hq t s

end ColibTest.ScalarCofiberAdditivitySquare

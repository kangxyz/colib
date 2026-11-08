/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberSequenceMap
public import Colib.KTheory.Waldhausen.Additivity.BasedTransformationSquare

/-! # The literal scalar map of full based-additivity squares

The accepted identity-to-scalar sequence map specializes the original subdivided full square.
Its four entire faces retain both original additivity paths, the rebased inclusion cylinder,
and the actual quotient-first normalized zero-to-cone sum cylinder. Implementation provenance:
    Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberAdditivitySquare.lean:34-182
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Both continuous times fix
the original chosen zero. Projection/null alignment and the signed fiber comparison are separate.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
    CategoryTheory.Waldhausen.Fibration
open SSet
open scoped Simplicial Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

local instance scalarAdditivityCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
    (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The whole actual normalized inclusion cylinder on the ordinary diagonal. -/
def perfectOpenScalarInclusionDiagonalHomotopy :
    SSet.Homotopy
      (SSet.diagonalMap (bisimplicialSSetMap (RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace).cof
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
          (perfectOpenScalarIdentityCofibrationSequence j).exactG.rebase))
      (SSet.diagonalMap (bisimplicialSSetMap (RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace).cof
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
          (perfectOpenScalarCofibrationSequence j r).exactG.rebase)) :=
  normalizedMiddleTransformationHomotopy (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenNested j).coarse
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (perfectScalarInclusionNat X r) (perfectScalarInclusionNat_openWeak j r q hq)

/-- The whole actual quotient-first normalized zero-to-cone and identity sum cylinder. -/
def perfectOpenScalarSumDiagonalHomotopy :
    SSet.Homotopy
      (SSet.diagonalMap (normalizedSumMap (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenNested j).coarse
        (perfectOpenScalarIdentityCofibrationSequence j).exactH
        (perfectOpenScalarIdentityCofibrationSequence j).exactF))
      (SSet.diagonalMap (normalizedSumMap (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenNested j).coarse
        (perfectOpenScalarCofibrationSequence j r).exactH
        (perfectOpenScalarCofibrationSequence j r).exactF)) :=
  normalizedSumTransformationHomotopy (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenNested j).coarse
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K)
      (perfectOpenScalarZeroToCone j r q hq) (perfectOpenScalarZeroToCone_weak j r q hq)

/-- The literal full square at the original identity-to-scalar sequence map. -/
def perfectOpenScalarBasedAdditivitySquare :
    C(unitInterval × (unitInterval × |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙
      bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|),
        |SSet.diagonalSSet (bisimplicialSSet
      (perfectOpenNested j).coarse)|) :=
  subdividedBasedAdditivityTransformationSquare (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace) (perfectOpenNested j).coarse
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq)

/-- The construction uses the exact original transformations and the complete old pasting. -/
theorem perfectOpenScalarBasedAdditivitySquare_eq :
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
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) := rfl

/-- The entire transformation-zero face is the specified identity-sequence additivity path. -/
theorem perfectOpenScalarBasedAdditivitySquare_transformation_zero (s : unitInterval)
    (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (0, (s, x)) =
      subdividedBasedAdditivityHomotopy (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenNested j).coarse (𝟙 (𝟭
        (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
          (QuotientRows.oneIdToZero (perfectOpenNested j).coarse)
        (perfectOpenScalarIdentityCofibrationSequence j) (s, x) :=
  subdividedBasedAdditivityTransformationSquare_transformation_zero
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenNested j).coarse
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) s x

/-- The entire transformation-one face is the specified actual scalar-sequence additivity path. -/
theorem perfectOpenScalarBasedAdditivitySquare_transformation_one (s : unitInterval)
    (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (1, (s, x)) =
      subdividedBasedAdditivityHomotopy (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenNested j).coarse
        (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
        (perfectOpenScalarCofibrationSequence j r) (s, x) :=
  subdividedBasedAdditivityTransformationSquare_transformation_one
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenNested j).coarse
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) s x

/-- The complete initial face keeps the normalized inclusion on actual first-half restriction. -/
theorem perfectOpenScalarBasedAdditivitySquare_additivity_zero (t : unitInterval)
    (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (t, (0, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarInclusionDiagonalHomotopy j r q hq)
        (t, (realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet
          (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))) x) :=
  subdividedBasedAdditivityTransformationSquare_additivity_zero
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenNested j).coarse
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) t x

/-- The complete terminal face keeps both half restrictions and the quotient-first normalization. -/
theorem perfectOpenScalarBasedAdditivitySquare_additivity_one (t : unitInterval)
    (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|) :
    perfectOpenScalarBasedAdditivitySquare j r q hq (t, (1, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarSumDiagonalHomotopy j r q hq) (t, x) :=
  subdividedBasedAdditivityTransformationSquare_additivity_one
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenNested j).coarse
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r)
    (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) (perfectScalarConeProjectionNat X r)
    (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (perfectScalarInclusionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    (by simp only [Category.id_comp])
    (perfectOpenScalarZeroToCone_sequence j r q hq)
    (fun K ↦ (perfectOpenNested j).coarse.weq.id_mem K) (perfectScalarInclusionNat_openWeak j r q
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) t x

/-- Both original continuous times fix the actual subdivided zero vertex. -/
theorem perfectOpenScalarBasedAdditivitySquare_fixed_zero (t s : unitInterval) :
    perfectOpenScalarBasedAdditivitySquare j r q hq
      (t, (s, subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))) =
        realizationPoint (diagonalZeroVertex (perfectOpenNested j).coarse) :=
  subdividedBasedAdditivityTransformationSquare_fixed_zero (RingedSpace.perfectComplexesWaldhausen
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
      hq) (perfectOpenScalarZeroToCone_weak j r q hq) t s

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0303",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberAdditivitySquare.lean:64-182"
    "adaptation" "The native scalar square with all four whole faces and chosen-zero surface"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarBasedAdditivitySquare
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarBasedAdditivitySquare_transformation_zero
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarBasedAdditivitySquare_transformation_one
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarBasedAdditivitySquare_additivity_zero
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarBasedAdditivitySquare_additivity_one
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarBasedAdditivitySquare_fixed_zero

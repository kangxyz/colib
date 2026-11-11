/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.Scheme.CoefficientLaurentProjection

/-! # Original integral Spec and coefficient comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
universe u
namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow

/-- The structural map of an integral algebra is the original terminal map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseCoefficientRow.lean:30"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem coefficient_terminal (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Spec.map a.hom = specULiftZIsTerminal.from (Spec a.right) :=
  specULiftZIsTerminal.hom_ext _ _

/-- The original coefficient fiber differs from the parameter product by symmetry. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseCoefficientRow.lean:35"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
def rowIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    space (op Q, a) ≅ (baseProductFunctor Q.hom).obj (Spec a.right) :=
  pullbackSymmetry Q.hom (Spec.map a.hom) ≪≫
    pullback.congrHom (coefficient_terminal a) rfl

/-- The parameter projection is exactly the original coefficient projection. -/
@[reassoc,
  colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseCoefficientRow.lean:42"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem rowIso_fst (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (rowIso Q a).hom ≫ pullback.fst _ _ = coefficientProjection (op Q, a) := by
  simp [rowIso, pullback.congrHom]

/-- The fixed-factor projection is exactly the original scheme projection. -/
@[reassoc,
  colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseCoefficientRow.lean:48"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem rowIso_snd (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (rowIso Q a).hom ≫ pullback.snd _ _ = projection (op Q, a) := by
  simp [rowIso, pullback.congrHom]

/-- Scheme restriction preserves the entire two-projection comparison. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseCoefficientRow.lean:54"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem rowIso_scheme {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    schemeMap f a ≫ (rowIso Q a).hom =
      (rowIso P a).hom ≫
        (baseProductTransformation P.hom Q.hom f.left (Over.w f)).app (Spec a.right) := by
  apply pullback.hom_ext
  · simp [Category.assoc, rowIso_fst, schemeMap_coefficientProjection,
      baseProductTransformation]
  · simp [Category.assoc, rowIso_snd, rowIso_snd_assoc,
      schemeMap_projection, baseProductTransformation]

/-- Coefficient restriction preserves the original parameter-product row. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseCoefficientRow.lean:66"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem rowIso_coefficient (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (f : a ⟶ b) :
    coefficientMap Q f ≫ (rowIso Q a).hom =
      (rowIso Q b).hom ≫ (baseProductFunctor Q.hom).map (Spec.map f.right) := by
  apply pullback.hom_ext
  · simp [Category.assoc, rowIso_fst, rowIso_fst_assoc, coefficientMap_coefficientProjection,
      baseProductFunctor]
  · simp [Category.assoc, rowIso_snd, coefficientMap, map_projection, baseProductFunctor]

/-- At the original identity algebra, the parameter product returns the fixed scheme. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseCoefficientRow.lean:76"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
def identityIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (baseProductFunctor Q.hom).obj (Spec (CommRingCat.of (ULift.{u} ℤ))) ≅ Q.left :=
  (rowIso Q (Under.mk (𝟙 _))).symm ≪≫ identityProjectionIso Q

/-- The basepoint comparison keeps the actual fixed-factor projection. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseCoefficientRow.lean:81"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem identityIso_hom (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    (identityIso Q).hom = pullback.snd _ _ := by
  apply (Iso.inv_comp_eq (rowIso Q (Under.mk (𝟙 _)))).2
  exact (rowIso_snd Q (Under.mk (𝟙 _))).symm

end AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow


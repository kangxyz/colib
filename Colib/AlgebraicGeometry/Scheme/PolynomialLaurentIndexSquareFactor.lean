/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentIndexSquare

/-!
# Actual factor-variable naturality of the Bass index interchange

The second-factor projection and positive/inverse factor maps commute with the
four-corner index isomorphism. All maps are the original arbitrary-scheme products.
These equations assemble the finite geometric Bass square interchange.
Intended owner: Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IndexSquare.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
universe u
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

/-- Apply a natural transformation to all four original corners of a square. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquareFactor.lean:28"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def onSquare {F G : Scheme.{u}ᵒᵖ ⥤ Scheme.{u}ᵒᵖ} (a : F ⟶ G)
    (S : Arrow (Arrow Scheme.{u}ᵒᵖ)) :
    F.mapArrow.mapArrow.obj S ⟶ G.mapArrow.mapArrow.obj S :=
  ((Functor.mapArrowFunctor (Arrow Scheme.{u}ᵒᵖ) (Arrow Scheme.{u}ᵒᵖ)).map
    ((Functor.mapArrowFunctor Scheme.{u}ᵒᵖ Scheme.{u}ᵒᵖ).map a)).app S

variable {T T' : Scheme.{u}} (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (q' : T' ⟶ (Spec (.of
    (ULift.{u} ℤ))))
  (f : T ⟶ T') (hf : f ≫ q' = q)

/-- Changing the actual fixed factor commutes with all four original swap components. -/
@[colib_tag "COL-0532", colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquareFactor.lean:38"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem squareIso_factor (X : Scheme.{u}ᵒᵖ) :
    squareFunctor.map ((baseProductTransformation q q' f hf).app X.unop).op ≫
        (squareIso q X).hom =
      (squareIso q' X).hom ≫
        onSquare (NatTrans.op (baseProductTransformation q q' f hf)) (square X) := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext
  · change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_transformation_second _ q q' f hf X.unop).symm
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_transformation_second _ q q' f hf X.unop).symm
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_transformation_second _ q q' f hf X.unop).symm

/-- The actual factor projection gives the unchanged source leg after index interchange. -/
@[colib_tag "COL-0532", colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquareFactor.lean:55"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem squareIso_projection (X : Scheme.{u}ᵒᵖ) :
    squareFunctor.map ((baseProductProjection q).app X.unop).op ≫
        (squareIso q X).hom =
      onSquare (NatTrans.op (baseProductProjection q)) (square X) := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext
  · change _ ≫ 𝟙 _ = _
    simp only [Category.comp_id]
    rfl
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_projection_second _ q X.unop)
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_projection_second _ q X.unop)
  · exact Quiver.Hom.unop_inj
      (baseProductSwapIso_projection_second _ q X.unop)

/-- The original positive factor chart retains the same four-corner isomorphisms. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquareFactor.lean:71"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem squareIso_plus (X : Scheme.{u}ᵒᵖ) :
    squareFunctor.map (plus.app X.unop).op ≫
        (squareIso (laurentProjection (.of (ULift.{u} ℤ))) X).hom =
      (squareIso (polynomialProjection (.of (ULift.{u} ℤ))) X).hom ≫
        onSquare (NatTrans.op plus) (square X) := squareIso_factor _ _ _ _ X

/-- The original inverted factor chart retains the same four-corner isomorphisms. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IndexSquareFactor.lean:78"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem squareIso_minus (X : Scheme.{u}ᵒᵖ) :
    squareFunctor.map (minus.app X.unop).op ≫
        (squareIso (laurentProjection (.of (ULift.{u} ℤ))) X).hom =
      (squareIso (polynomialProjection (.of (ULift.{u} ℤ))) X).hom ≫
        onSquare (NatTrans.op minus) (square X) := squareIso_factor _ _ _ _ X

end AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex


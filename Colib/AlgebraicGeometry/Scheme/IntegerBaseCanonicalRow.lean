/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseParameterRow

/-! # Original integral Spec and coefficient comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow

/-- The specified integral structure morphism is the canonical terminal map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseCanonicalRow.lean:33"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem structure_terminal (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    Q.hom = specULiftZIsTerminal.from Q.left := specULiftZIsTerminal.hom_ext _ _

/-- The actual coefficient fiber maps to the literal global parameter-product object. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseCanonicalRow.lean:37"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
def canonicalRowIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    space (op Q, a) ≅ (baseProductFunctor (specULiftZIsTerminal.from Q.left)).obj (Spec a.right) :=
  rowIso Q a ≪≫ pullback.congrHom rfl (structure_terminal Q)

/-- The canonical row comparison retains the coefficient projection. -/
@[reassoc, colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseCanonicalRow.lean:43"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem canonicalRowIso_fst (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (canonicalRowIso Q a).hom ≫ pullback.fst _ _ = coefficientProjection (op Q, a) := by
  simp [canonicalRowIso, pullback.congrHom, rowIso_fst]

/-- The canonical row comparison retains the fixed-factor projection. -/
@[reassoc, colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseCanonicalRow.lean:49"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem canonicalRowIso_snd (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (canonicalRowIso Q a).hom ≫ pullback.snd _ _ = projection (op Q, a) := by
  simp [canonicalRowIso, pullback.congrHom, rowIso_snd]

/-- Every original coefficient map respects the literal global parameter endpoint. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseCanonicalRow.lean:55"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem canonicalRowIso_coefficient (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (f : a ⟶ b) :
    coefficientMap Q f ≫ (canonicalRowIso Q a).hom =
      (canonicalRowIso Q b).hom ≫
        (baseProductFunctor (specULiftZIsTerminal.from Q.left)).map (Spec.map f.right) := by
  apply pullback.hom_ext
  · simp [Category.assoc, canonicalRowIso_fst, canonicalRowIso_fst_assoc,
      coefficientMap_coefficientProjection, baseProductFunctor]
  · simp [Category.assoc, canonicalRowIso_snd, coefficientMap,
      map_projection, baseProductFunctor]

/-- The exact geometric row isomorphism ready for the original global Model functor. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseCanonicalRow.lean:67"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
def canonicalParameterRowIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ (baseProductFunctor (specULiftZIsTerminal.from Q.left)).op ≅
      row Q ⋙ functor (CommRingCat.of (ULift.{u} ℤ)) :=
  NatIso.ofComponents (fun a => (canonicalRowIso Q a).op) (fun f =>
    Quiver.Hom.unop_inj (canonicalRowIso_coefficient Q f).symm)

/-- The original fixed-pair arrow commutes with the entire canonical row comparison. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseCanonicalRow.lean:74"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem canonicalRowIso_scheme {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    schemeMap f a ≫ (canonicalRowIso Q a).hom =
      (canonicalRowIso P a).hom ≫
        (baseProductTransformation (specULiftZIsTerminal.from P.left) (specULiftZIsTerminal.from
          Q.left)
          f.left (specULiftZIsTerminal.hom_ext _ _)).app (Spec a.right) := by
  apply pullback.hom_ext
  · simp [Category.assoc, canonicalRowIso_fst, schemeMap_coefficientProjection,
      baseProductTransformation]
  · simp [Category.assoc, canonicalRowIso_snd, canonicalRowIso_snd_assoc,
      schemeMap_projection, baseProductTransformation]

/-- The literal global endpoint preserves every original coefficient unit. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseCanonicalRow.lean:87"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem canonicalRowIso_unit (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (v : (Γ(Spec a.right, ⊤))ˣ) :
    Units.map (canonicalRowIso Q a).hom.appTop.hom.toMonoidHom
      (Units.map (pullback.fst (specULiftZIsTerminal.from (Spec a.right))
        (specULiftZIsTerminal.from Q.left)).appTop.hom.toMonoidHom v) =
      Units.map (coefficientProjection (op Q, a)).appTop.hom.toMonoidHom v := by
  apply Units.ext
  have h := congrArg (fun g => g.appTop) (canonicalRowIso_fst Q a)
  rw [Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑v)

end AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow


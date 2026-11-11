/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseSpecSquare
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseCoefficientRow

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

/-- Parameter-first products and the original coefficient fibers form isomorphic rows. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseParameterRow.lean:32"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
def parameterRowIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ (baseProductFunctor Q.hom).op ≅
      row Q ⋙ functor (CommRingCat.of (ULift.{u} ℤ)) :=
  NatIso.ofComponents (fun a => (rowIso Q a).op) (fun f =>
    Quiver.Hom.unop_inj (rowIso_coefficient Q f).symm)

/-- The row isomorphism preserves the actual restriction arrow of the fixed pair. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseParameterRow.lean:39"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem parameterRowIso_scheme {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((baseProductTransformation P.hom Q.hom f.left (Over.w f)).app (Spec a.right)).op ≫
        (parameterRowIso P).hom.app a =
      (parameterRowIso Q).hom.app a ≫ (schemeMap f a).op :=
  Quiver.Hom.unop_inj (rowIso_scheme f a).symm

/-- Symmetry preserves the complete coefficient unit, with no coordinate inversion. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseParameterRow.lean:47"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem rowIso_unit (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (v : (Γ(Spec a.right, ⊤))ˣ) :
    Units.map (rowIso Q a).hom.appTop.hom.toMonoidHom
      (Units.map (pullback.fst (specULiftZIsTerminal.from (Spec a.right))
        Q.hom).appTop.hom.toMonoidHom v) =
      Units.map (coefficientProjection (op Q, a)).appTop.hom.toMonoidHom v := by
  apply Units.ext
  have h := congrArg (fun g => g.appTop) (rowIso_fst Q a)
  rw [Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑v)

end AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow


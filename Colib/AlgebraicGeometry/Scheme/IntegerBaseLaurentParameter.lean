/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseCanonicalRow

/-! # Original integral Spec and coefficient comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow

/-- The full original Laurent coefficient fiber maps to the actual parameter Laurent product. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseLaurentParameter.lean:35"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
def laurentParameterIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    space (op Q, (laurentUnderFunctor _).obj a) ≅
      (baseProductFunctor (specULiftZIsTerminal.from Q.left)).obj
        (GlobalIndex.laurent.obj (Spec a.right)) :=
  canonicalRowIso Q ((laurentUnderFunctor _).obj a) ≪≫
    (baseProductFunctor (specULiftZIsTerminal.from Q.left)).mapIso (laurentSpecIso a.right)

/-- The actual parameter projection retains the complete affine Laurent comparison. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseLaurentParameter.lean:44"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem laurentParameterIso_projection (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (laurentParameterIso Q a).hom ≫
        (baseProductProjection (specULiftZIsTerminal.from Q.left)).app
          (GlobalIndex.laurent.obj (Spec a.right)) =
      coefficientProjection (op Q, (laurentUnderFunctor _).obj a) ≫
        (laurentSpecIso a.right).hom := by
  simp only [laurentParameterIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [(baseProductProjection (specULiftZIsTerminal.from Q.left)).naturality]
  exact canonicalRowIso_fst_assoc Q _ _

/-- Pulling back units reverses the two actual geometric arrows. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseLaurentParameter.lean:56"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem unitPullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (v : (Γ(Z, ⊤))ˣ) :
    Units.map f.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom v) =
      Units.map (f ≫ g).appTop.hom.toMonoidHom v := by
  ext
  simp

/-- The complete parameter Laurent comparison preserves the original coefficient T unit. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/IntegerBaseLaurentParameter.lean:64"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem laurentParameterIso_unit (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Units.map (laurentParameterIso Q a).hom.appTop.hom.toMonoidHom
      (Units.map ((baseProductProjection (specULiftZIsTerminal.from Q.left)).app
        (GlobalIndex.laurent.obj (Spec a.right))).appTop.hom.toMonoidHom
          (Units.map (pullback.snd (specULiftZIsTerminal.from (Spec a.right))
            (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u}
              ℤ)))).appTop.hom.toMonoidHom
              (laurentCoordinate (CommRingCat.of (ULift.{u} ℤ))))) =
      Units.map (coefficientProjection (op Q, (laurentUnderFunctor _).obj a)).appTop.hom.toMonoidHom
        (laurentCoordinate a.right) := by
  rw [unitPullback_comp, laurentParameterIso_projection, ← unitPullback_comp]
  exact congrArg (Units.map (coefficientProjection
    (op Q, (laurentUnderFunctor _).obj a)).appTop.hom.toMonoidHom)
    (nativeLaurentUnit_spec a.right)

end AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow


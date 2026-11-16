/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.PositiveBassQuotient
public import Mathlib.Algebra.Category.Grp.Colimits

/-! # The canonical inverse Laurent unit in the categorical Bass quotient -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] Waldhausen.Additivity.KCommGroup

local notation "W" Y =>
  RingedSpace.perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace
    (Scheme.toLocallyRingedSpace Y))

/-- The original geometric difference, expressed as a morphism of additive groups. -/
def positiveBassDifferenceHom (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    AddCommGrpCat.of (Additive ((W(Relative.polynomialFunctor.obj X).obj).K n ×
      (W(Relative.polynomialFunctor.obj X).obj).K n)) ⟶
        AddCommGrpCat.of (Additive ((W(Relative.laurentFunctor.obj X).obj).K n)) :=
  AddCommGrpCat.ofHom (relativeLaurentDifference X n).toAdditive

/-- The unchanged inverse Laurent unit, in the original categorical chart cokernel. -/
def positiveBassInverseQuotientHom (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    AddCommGrpCat.of (Additive ((W X.obj).K n)) ⟶
      cokernel (positiveBassDifferenceHom X (n + 1)) :=
  AddCommGrpCat.ofHom (positiveBassUnitSection X n).toAdditive ≫
    cokernel.π (positiveBassDifferenceHom X (n + 1))

/-- The actual inverse-coordinate operation is an isomorphism onto the original cokernel. -/
instance (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj] (n : ℕ) :
    IsIso (positiveBassInverseQuotientHom X n) := by
  let e := AddCommGrpCat.cokernelIsoQuotient (positiveBassDifferenceHom X (n + 1))
  have he : positiveBassInverseQuotientHom X n ≫ e.hom =
      (positiveBassQuotientEquiv X n).symm.toAdditive.toAddCommGrpIso.hom := by
    apply AddCommGrpCat.ext
    intro x
    let f := positiveBassDifferenceHom X (n + 1)
    let q := AddCommGrpCat.ofHom (QuotientAddGroup.mk' f.hom.range)
    have hq : f ≫ q = 0 := by
      ext z
      simp [q]
    have h := ConcreteCategory.congr_hom (cokernel.π_desc f q hq)
      (Additive.ofMul (positiveBassUnitSection X n x.toMul))
    change (e.hom ((cokernel.π (positiveBassDifferenceHom X (n + 1)))
      (Additive.ofMul (positiveBassUnitSection X n x.toMul)))) = _
    exact h.trans (congrArg Additive.ofMul
      (positiveBassQuotientEquiv_symm_apply X n x.toMul)).symm
  let : IsIso (positiveBassInverseQuotientHom X n ≫ e.hom) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ e.hom

end AlgebraicGeometry.Scheme.ProjectiveLine

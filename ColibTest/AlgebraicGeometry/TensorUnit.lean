/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitPullback
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitEdge

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
variable (X Y : Scheme.{u}) (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

example : boundedAboveFlatPerfectTensorUnit X ≅
    𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  boundedAboveFlatPerfectTensorUnitIso X

example : boundedAboveFlatPerfectTensorUnitPullback f ≅ boundedAboveFlatPerfectPullback f :=
  boundedAboveFlatPerfectTensorUnitPullbackIso f

example : (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom ≫
    (boundedAboveFlatPerfectTensorUnitPullbackIso f).hom =
    (boundedAboveFlatPerfectTensorUnitPullbackIso f).hom ≫
      (boundedAboveFlatPerfectPullbackUnitIso f r).hom :=
  boundedAboveFlatPerfectTensorUnitPullbackAutomorphism_unitor f r

example : complexTensorUnitCoefficientEdge X r =
    ComposableArrows.mk₁ (complexTensorUnitAutomorphism X r).hom :=
  complexTensorUnitCoefficientEdge_eq X r

example (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (((complexTensorUnitCoefficientEdge X r).map
      (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).app K).f n =
      ((complexTensorUnitAutomorphism X r).hom.app K).f n := rfl

example : (complexTensorUnitAutomorphism X r).hom ≫ (complexTensorUnitIso X).hom =
    (complexTensorUnitIso X).hom ≫ (complexGlobalUnitIso X r).hom :=
  complexTensorUnitAutomorphism_unitor X r

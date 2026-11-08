/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.PerfectOppositeWeakArrow

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace
noncomputable section
universe u

example (X : RingedSpace.{u, u}) :
    Waldhausen.IsCompatibleDual (perfectComplexesWaldhausen X)
      (perfectComplexesOppositeWaldhausen X) :=
  perfectComplexesOppositeWaldhausen_compatible X

example {X : RingedSpace.{u, u}}
    {K L : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ}
    (f : K ⟶ L) [Epi f] (hK : IsPerfectComplex K) (hL : IsPerfectComplex L) :
    IsPerfectComplex (kernel f) :=
  isPerfectComplex_X₁_of_shortExact X
    (S := ShortComplex.mk (kernel.ι f) f (kernel.condition f))
    { exact := ShortComplex.kernelSequence_exact f } hK hL

open AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

example : Waldhausen.IsExact (perfectComplexesOppositeWaldhausen X.toRingedSpace).cof
    (perfectComplexesOppositeWaldhausen X.toRingedSpace).weq
    (perfectComplexesOppositeWaldhausen Y.toRingedSpace).cof
    (perfectComplexesOppositeWaldhausen Y.toRingedSpace).weq
    (perfectComplexesRestrictOpenImmersion j).op :=
  perfectComplexesRestrictOpenImmersion_op_exact j

example (f : Arrow (ObjectProperty.FullSubcategory
    (IsPerfectComplex (X := X.toRingedSpace)))ᵒᵖ) :
    ((perfectComplexesRestrictOpenImmersionJointIso j).inv.app f).hom.right ≫
      (perfectComplexesRestrictOpenImmersion j).op.map
        ((perfectComplexesOppositeJointData X.toRingedSpace).projection.app f) =
    (perfectComplexesOppositeJointData Y.toRingedSpace).projection.app
      ((perfectComplexesRestrictOpenImmersion j).op.mapArrow.obj f) :=
  perfectComplexesRestrictOpenImmersionJointIso_inv_projection j f

example {K L : ObjectProperty.FullSubcategory
    (IsPerfectComplex (X := X.toRingedSpace))} (f : K ⟶ L) (n : ℤ) :
    (((perfectComplexesRestrictOpenImmersion j).map f).hom).f n =
      (restrictFunctor j).map (f.hom.f n) := rfl

example : Waldhausen.Fibration.RowFactorization.JointData
    (Waldhausen.Fibration.NestedWeakEquivalences.refl
      (perfectComplexesRestrictWeakArrowOppositeWaldhausen j)) :=
  perfectComplexesRestrictWeakArrowOppositeJointData j

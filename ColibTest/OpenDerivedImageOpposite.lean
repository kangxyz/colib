/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.WeakArrowLift

/-! Regression checks for the actual opposite image, strict maps and component kernels. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j)]

example {K L : Obj j} (f : K ⟶ L) :
    (oppositeWaldhausen j).cof f.op ↔ Epi f.hom := deflation_iff j f

example : IsCompatibleDual (waldhausen j Fact.out) (oppositeWaldhausen j) :=
  oppositeWaldhausen_compatible j

example : Fibration.RowFactorization.JointData
    (Fibration.NestedWeakEquivalences.refl (weakArrowOppositeWaldhausen j)) :=
  weakArrowOppositeJointData j

example {Z : WeakArrow.Obj (waldhausen j Fact.out) (corestrict j)} {B : Obj j}
    (b : B ⟶ (WeakArrow.target (waldhausen j Fact.out) (corestrict j)).obj Z) :
    ∃ (Y : WeakArrow.Obj (waldhausen j Fact.out) (corestrict j)) (f : Y ⟶ Z)
      (v : B ⟶ (WeakArrow.target (waldhausen j Fact.out) (corestrict j)).obj Y),
      (weakArrowOppositeWaldhausen j).cof.unop f ∧ (waldhausen j Fact.out).weq v ∧
      v ≫ (WeakArrow.target (waldhausen j Fact.out) (corestrict j)).map f = b :=
  weakArrow_target_lift j b

example (f : Arrow (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))ᵒᵖ) :
    (oppositeJointData j).inl.app ((corestrict j).op.mapArrow.obj f) ≫
      ((corestrictJointIso j).inv.app f).hom.left =
    (corestrict j).op.map ((RingedSpace.perfectComplexesOppositeJointData
      X.toRingedSpace).inl.app f) := corestrictJointIso_inv_inl j f

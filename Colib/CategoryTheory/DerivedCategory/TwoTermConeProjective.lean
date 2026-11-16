/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Projective terms of a shifted two-term cone -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace CochainComplex

attribute [local instance] Abelian.hasFiniteBiproducts

variable {R : Type u} [CommRing R]

private theorem projective_single_X (A : ModuleCat.{u} R) [Module.Projective R A] (n : ℤ) :
    Module.Projective R (((single (ModuleCat.{u} R) (.up ℤ) 0).obj A).X n) := by
  by_cases hn : n = 0
  · subst n
    exact Module.Projective.of_equiv (singleObjXSelf (.up ℤ) 0 A).symm.toLinearEquiv
  · let E := ((single (ModuleCat.{u} R) (.up ℤ) 0).obj A).X n
    have hE : IsZero E := isZero_single_obj_X _ _ _ _ hn
    let : Projective E := hE.projective
    infer_instance

private theorem projective_biprod (A B : ModuleCat.{u} R)
    [Module.Projective R A] [Module.Projective R B] :
    Module.Projective R ((A ⊞ B : ModuleCat.{u} R) : Type u) :=
  Module.Projective.of_equiv (ModuleCat.biprodIsoProd A B).symm.toLinearEquiv

/-- A cone of a map between projective modules placed in degree zero, shifted to degrees
zero and one, has projective terms. -/
theorem projective_shiftedMappingCone_single (A B : ModuleCat.{u} R)
    [Module.Projective R A] [Module.Projective R B] (f : A ⟶ B) (n : ℤ) :
    Module.Projective R
      (((mappingCone ((single (ModuleCat.{u} R) (.up ℤ) 0).map f))⟦(-1 : ℤ)⟧).X n) := by
  let S := single (ModuleCat.{u} R) (.up ℤ) 0
  let D := mappingCone (S.map f)
  let e := D.shiftFunctorObjXIso (-1) n (n - 1) (by omega)
  let e' := HomologicalComplex.homotopyCofiber.XIsoBiprod (S.map f) (n - 1)
    (n - 1 + 1) rfl
  let : Module.Projective R ((S.obj A).X (n - 1 + 1)) := projective_single_X A _
  let : Module.Projective R ((S.obj B).X (n - 1)) := projective_single_X B _
  let := projective_biprod ((S.obj A).X (n - 1 + 1)) ((S.obj B).X (n - 1))
  exact Module.Projective.of_equiv (e ≪≫ e').symm.toLinearEquiv

end CochainComplex

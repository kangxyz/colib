/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModulesFunctor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Torsion sheaf complexes as complexes of modules

This uses the existing torsion-sheaf coefficient functor. The underlying abelian
sheaf complex is unchanged up to its canonical natural isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

universe t s v u

namespace Stacks.Cohomology.ZModSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)

/-- Abelian sheaves whose sections are annihilated by the coefficient level. -/
def torsionSheafProperty : ObjectProperty (Sheaf J AddCommGrpCat.{t}) :=
  fun F => ∀ (X : Cᵒᵖ) (x : ToType (F.obj.obj X)), n • x = 0

/-- A termwise torsion complex, valued in the full category of torsion sheaves. -/
def torsionComplexLift (K : CochainComplex (Sheaf J AddCommGrpCat.{t}) ℤ)
    (hK : ∀ i, torsionSheafProperty J n (K.X i)) :
    CochainComplex (torsionSheafProperty J n).FullSubcategory ℤ where
  X i := ⟨K.X i, hK i⟩
  d i j := ObjectProperty.homMk (K.d i j)
  shape i j h := ObjectProperty.hom_ext _ (K.shape i j h)
  d_comp_d' i j k _ _ := ObjectProperty.hom_ext _ (K.d_comp_d i j k)

variable [HasSheafify J CommRingCat.{s}]
  [J.WEqualsLocallyBijective CommRingCat.{s}]
  [HasWeakSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- The existing coefficient functor restricted to the full torsion subcategory. -/
def torsionSheafCoefficientFunctor :
    (torsionSheafProperty J n).FullSubcategory ⥤ SheafOfModules.{t} (zmodRingSheaf.{s} J n) :=
  torsionSheafToModulesFunctor J n (torsionSheafProperty J n).ι (fun F => F.property)

/-- The torsion coefficient functor is additive. -/
instance torsionSheafCoefficientFunctor_additive :
    (torsionSheafCoefficientFunctor.{t, s} J n).Additive := by
  unfold torsionSheafCoefficientFunctor
  exact torsionSheafToModulesFunctor_additive J n
    (torsionSheafProperty J n).ι (fun F => F.property)

/-- A termwise torsion sheaf complex canonically read over the constant coefficient ring. -/
def torsionComplexToModules (K : CochainComplex (Sheaf J AddCommGrpCat.{t}) ℤ)
    (hK : ∀ i, torsionSheafProperty J n (K.X i)) :
    CochainComplex (SheafOfModules.{t} (zmodRingSheaf.{s} J n)) ℤ :=
  ((torsionSheafCoefficientFunctor.{t, s} J n).mapHomologicalComplex (.up ℤ)).obj
    (torsionComplexLift J n K hK)

/-- Forgetting coefficients recovers the original torsion complex. -/
def torsionComplexToModulesUnderlyingIso
    (K : CochainComplex (Sheaf J AddCommGrpCat.{t}) ℤ)
    (hK : ∀ i, torsionSheafProperty J n (K.X i)) :
    ((SheafOfModules.toSheaf (zmodRingSheaf.{s} J n)).mapHomologicalComplex (.up ℤ)).obj
        (torsionComplexToModules J n K hK) ≅ K :=
  letI : (torsionSheafToModulesFunctor.{t, s} J n
    (torsionSheafProperty J n).ι (fun F => F.property)).Additive :=
      torsionSheafCoefficientFunctor_additive J n
  (Functor.mapHomologicalComplexCompIso
    (torsionSheafToModulesFunctorCompToSheaf J n
      (torsionSheafProperty J n).ι (fun F => F.property)) (.up ℤ)).app
        (torsionComplexLift J n K hK)

end Stacks.Cohomology.ZModSheaf

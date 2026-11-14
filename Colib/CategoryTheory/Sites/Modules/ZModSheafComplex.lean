/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Modules.ZModSheafModel

/-!
# Actual torsion complexes as coefficient-valued sheaf complexes

The coefficient-category equivalence preserves the underlying complex, including its
original differential. No derived fullness is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory

universe t s v u

namespace Stacks.Cohomology.ZModSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)
variable [HasSheafify J CommRingCat.{s}]
  [J.WEqualsLocallyBijective CommRingCat.{s}]
  [HasWeakSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{t} (ULift.{s} (ZMod n))) AddCommGrpCat.{t})]

/-- Forgetting constant coefficients preserves addition. -/
instance coefficientForget_additive :
    (sheafCompose J (forget₂ (ModuleCat.{t} (ULift.{s} (ZMod n)))
      AddCommGrpCat.{t})).Additive where
  map_add := rfl

/-- The actual torsion complex, read in the module-valued sheaf category. -/
def torsionComplexModuleSheaf (K : CochainComplex (Sheaf J AddCommGrpCat.{t}) ℤ)
    (hK : ∀ i, torsionSheafProperty J n (K.X i)) :=
  ((zmodModuleSheafEquivalence.{t, s} J n).functor.mapHomologicalComplex (.up ℤ)).obj
    (torsionComplexToModules J n K hK)

/-- The original torsion complex is recovered after forgetting constant coefficients. -/
def torsionComplexModuleSheafUnderlyingIso
    (K : CochainComplex (Sheaf J AddCommGrpCat.{t}) ℤ)
    (hK : ∀ i, torsionSheafProperty J n (K.X i)) :
    ((sheafCompose J (forget₂ (ModuleCat.{t} (ULift.{s} (ZMod n)))
        AddCommGrpCat.{t})).mapHomologicalComplex (.up ℤ)).obj
      (torsionComplexModuleSheaf J n K hK) ≅ K :=
  (Functor.mapHomologicalComplexCompIso
    (zmodModuleSheafForgetIso.{t, s} J n) (.up ℤ)).app
      (torsionComplexToModules J n K hK) ≪≫
    torsionComplexToModulesUnderlyingIso J n K hK

end Stacks.Cohomology.ZModSheaf

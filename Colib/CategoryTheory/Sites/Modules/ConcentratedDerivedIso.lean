/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Internal reconstruction of a concentrated complex

Truncation occurs inside the given abelian category. No forgetting of coefficients
or fullness of a derived forgetful functor is used.
-/

@[expose] public noncomputable section
open CategoryTheory
universe w v u

namespace DerivedCategory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A concentrated object is a single object of its own abelian category, its actual homology. -/
def concentratedHomologyIso (X : DerivedCategory C) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj X)  := Classical.choice (by
  obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let h : (homologyFunctor C n).obj X ≅ Y :=
    (homologyFunctor C n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C n).app Y
  exact ⟨e ≪≫ (singleFunctor C n).mapIso h.symm⟩)

/-- A concentrated complex is internally reconstructed from its actual complex homology. -/
def concentratedComplexHomologyIso (K : CochainComplex C ℤ) (n : ℤ)
    [K.IsGE n] [K.IsLE n] :
    Q.obj K ≅ (singleFunctor C n).obj (K.homology n) :=
  concentratedHomologyIso (Q.obj K) n ≪≫
    (singleFunctor C n).mapIso ((homologyFunctorFactors C n).app K)

end DerivedCategory

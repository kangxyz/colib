/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedFractionLift
public import Colib.AlgebraicGeometry.Modules.PerfectDerivedRoof

/-!
# Derived lifting on a supported two-open cover

The lift is constructed from a genuine fraction, exact extension by zero, and the actual
counit. The restriction equation is proved through the native derived-functor comparison.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u d₁ d₂

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d₁} X.Modules] [HasDerivedCategory.{d₂} U.Modules]

/-- Restrict a chain-map roof equation through the actual derived comparison. -/
theorem restrict_derived_roof_equation
    {M A B : CochainComplex X.Modules ℤ} (s : M ⟶ A) (t : M ⟶ B)
    (β : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B)
    (h : DerivedCategory.Q.map s ≫ β = DerivedCategory.Q.map t) :
    DerivedCategory.Q.map (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map s) ≫
        (restrictFunctor j).mapDerivedCategoryFactors.inv.app A ≫
        (restrictFunctor j).mapDerivedCategory.map β ≫
        (restrictFunctor j).mapDerivedCategoryFactors.hom.app B =
      DerivedCategory.Q.map (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map t) := by
  let F := (restrictFunctor j).mapDerivedCategory
  let e := (restrictFunctor j).mapDerivedCategoryFactors
  apply (cancel_epi (e.hom.app M)).1
  rw [← Category.assoc, ← (restrictFunctor j).mapDerivedCategoryFactors_hom_naturality s]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, h]
  exact (restrictFunctor j).mapDerivedCategoryFactors_hom_naturality t

/-- Every local derived arrow with a supported ambient source extends on a two-open cover.
The target is the original ambient complex and has no support or perfectness hypothesis. -/
theorem exists_supported_derived_lift (T : X.Opens)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
    (A B : CochainComplex X.Modules ℤ) (hA : perfectSupported T.ι A)
    (α : DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj A) ⟶
      DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj B)) :
    ∃ β : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B,
      (restrictFunctor j).mapDerivedCategoryFactors.inv.app A ≫
          (restrictFunctor j).mapDerivedCategory.map β ≫
          (restrictFunctor j).mapDerivedCategoryFactors.hom.app B = α := by
  obtain ⟨M, s, t, hs, ht⟩ := exists_supported_counit_fraction j T hcover A B hA α
  let : QuasiIso s := hs
  let β := inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map t
  refine ⟨β, ?_⟩
  have hβ : DerivedCategory.Q.map s ≫ β = DerivedCategory.Q.map t := by simp [β]
  have he := restrict_derived_roof_equation j s t β hβ
  exact (cancel_epi (DerivedCategory.Q.map
    (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map s))).1 (he.trans ht.symm)

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedExtensionByZero
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Lifting supported fractions across an open cover

The original ambient complexes are retained. A local fraction representative is extended
by zero, and the genuine counit supplies the ambient maps. Only the first ambient complex
is supported. The numerator target need not be perfect or supported. The triangle identity
identifies the restricted maps, rather than assuming a derived extension property.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AlgebraicGeometry.Scheme.Modules

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The adjunction unit identifies the restriction of a counit lift with the original map. -/
theorem extensionByZero_unit_restrict_counit_lift
    {N : CochainComplex U.Modules ℤ} {A : CochainComplex X.Modules ℤ}
    (s : N ⟶ ((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj A) :
    (Complex.extensionByZeroAdjunction j).unit.app N ≫
        ((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map
          ((Complex.extensionByZero j).map s ≫
            (Complex.extensionByZeroAdjunction j).counit.app A) = s := by
  let adj := Complex.extensionByZeroAdjunction j
  rw [Functor.map_comp, ← Category.assoc]
  change (adj.unit.app N ≫
      (Complex.extensionByZero j ⋙
        (restrictFunctor j).mapHomologicalComplex (.up ℤ)).map s) ≫ _ = s
  rw [← adj.unit.naturality s]
  simpa only [Functor.id_map, Category.assoc, Category.comp_id] using
    congrArg (s ≫ ·) (adj.right_triangle_components A)

/-- A local derived fraction with supported ambient source lifts to an ambient
quasi-isomorphism denominator. Its restriction represents exactly the original arrow.
The new ambient complex is only a fraction representative, not asserted perfect. -/
theorem exists_supported_counit_fraction
    [HasDerivedCategory.{d} U.Modules] (T : X.Opens)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
    (A B : CochainComplex X.Modules ℤ) (hA : perfectSupported T.ι A)
    (α : DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj A) ⟶
      DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj B)) :
    ∃ (M : CochainComplex X.Modules ℤ) (s : M ⟶ A) (t : M ⟶ B),
      QuasiIso s ∧
      DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map s) ≫ α =
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map t) := by
  let r := (restrictFunctor j).mapHomologicalComplex (.up ℤ)
  let e := Complex.extensionByZero j
  let adj := Complex.extensionByZeroAdjunction j
  obtain ⟨N, s, hs, t, hα⟩ := DerivedCategory.right_fac α
  have : QuasiIso s := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso] at hs
  have : QuasiIso (adj.counit.app A) :=
    extensionByZero_supported_counit_quasiIso j T hcover hA
  refine ⟨e.obj N, e.map s ≫ adj.counit.app A,
    e.map t ≫ adj.counit.app B, inferInstance, ?_⟩
  have hs' := extensionByZero_unit_restrict_counit_lift j s
  have ht' := extensionByZero_unit_restrict_counit_lift j t
  apply (cancel_epi (DerivedCategory.Q.map (adj.unit.app N))).1
  rw [← Category.assoc, ← Functor.map_comp, hs', ← Functor.map_comp, ht', hα]
  simp

end AlgebraicGeometry.Scheme.Modules

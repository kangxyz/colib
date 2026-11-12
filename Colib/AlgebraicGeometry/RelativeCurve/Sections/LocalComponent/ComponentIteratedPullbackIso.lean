/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # The exact iterated full-boundary pullback comparison -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

/-- Same actual component, with two successive chart/boundary pullbacks versus
the composite ambient map. This works for the full boundary scheme, not its support. -/
def componentIteratedPullbackIso {V C X T Z : Scheme.{u}}
    (κ : V ⟶ C) (F : C ⟶ X) (r : X ⟶ T) (d : Z ⟶ T) :
    pullback κ (pullback.fst F (pullback.fst r d)) ≅
      pullback κ (pullback.fst (F ≫ r) d) :=
  pullbackRightPullbackFstIso F (pullback.fst r d) κ ≪≫
    pullbackRightPullbackFstIso r d (κ ≫ F) ≪≫
    pullback.congrHom (Category.assoc κ F r) rfl ≪≫
    (pullbackRightPullbackFstIso (F ≫ r) d κ).symm

@[simp, reassoc] theorem componentIteratedPullbackIso_hom_fst
    {V C X T Z : Scheme.{u}} (κ : V ⟶ C) (F : C ⟶ X) (r : X ⟶ T) (d : Z ⟶ T) :
    (componentIteratedPullbackIso κ F r d).hom ≫
      pullback.fst κ (pullback.fst (F ≫ r) d) =
      pullback.fst κ (pullback.fst F (pullback.fst r d)) := by
  simp [componentIteratedPullbackIso, Iso.trans_hom, Category.assoc, pullback.congrHom_hom]

/-- A surjective boundary structure morphism stays the same surjective morphism
on the literal nested boundary used by the F-then-kappa root transport. -/
theorem surjective_component_iterated_boundary
    {V C X T Z A : Scheme.{u}} (κ : V ⟶ C) (F : C ⟶ X) (r : X ⟶ T)
    (d : Z ⟶ T) (q : C ⟶ A)
    [Surjective (pullback.fst κ (pullback.fst (F ≫ r) d) ≫ κ ≫ q)] :
    Surjective (pullback.fst κ (pullback.fst F (pullback.fst r d)) ≫ κ ≫ q) := by
  have h : Surjective ((componentIteratedPullbackIso κ F r d).hom ≫
      (pullback.fst κ (pullback.fst (F ≫ r) d) ≫ κ ≫ q)) := inferInstance
  simpa only [← Category.assoc, componentIteratedPullbackIso_hom_fst] using h

end AlgebraicGeometry.Scheme

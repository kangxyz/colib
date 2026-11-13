/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.SimplicialCylinder
public import Colib.CategoryTheory.Sites.Simplicial.SmashCylinder
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Pointed simplicial homotopies and the smash adjunction

The smash comparison identifies the original endpoints. The presheaf
adjunction therefore transposes each elementary simplicial homotopy.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

/-- An elementary homotopy through the actual pointed simplicial cylinder. -/
def CylinderHomotopic {X Y : PointedSimplicialPresheaf.{w} C} (f g : X ⟶ Y) : Prop :=
  ∃ h : parameterizedCylinder X (interval C) ⟶ Y,
    cylinderSection X (intervalEndpoint C 0) ≫ h = f ∧
      cylinderSection X (intervalEndpoint C 1) ≫ h = g

variable (T : PointedSimplicialPresheaf.{w} C)
  {G : PointedSimplicialPresheaf.{w} C ⥤ PointedSimplicialPresheaf.{w} C}
  (adj : Under.smashRightFunctor T ⊣ G)

/-- The actual pointed smash adjunction identifies elementary homotopies. -/
theorem cylinderHomotopic_homEquiv_iff {X Y : PointedSimplicialPresheaf.{w} C}
    (f g : (Under.smashRightFunctor T).obj X ⟶ Y) :
    CylinderHomotopic (adj.homEquiv X Y f) (adj.homEquiv X Y g) ↔
      CylinderHomotopic f g := by
  let F := Under.smashRightFunctor T
  let I := interval.{w} C
  let e : F.obj (parameterizedCylinder X I) ≅ parameterizedCylinder (F.obj X) I :=
    smashCylinderIso X T I
  let H := adj.homEquiv (parameterizedCylinder X I) Y
  have he (i : Fin 2) :
      F.map (cylinderSection X (intervalEndpoint C i)) ≫ e.hom =
        cylinderSection (F.obj X) (intervalEndpoint C i) :=
    smashMap_cylinderSection_smashCylinderIso_hom X T (intervalEndpoint C i)
  have hsection (i : Fin 2) :
      cylinderSection (F.obj X) (intervalEndpoint C i) ≫ e.inv =
        F.map (cylinderSection X (intervalEndpoint C i)) := by
    let a := F.map (cylinderSection X (intervalEndpoint C i))
    calc
      _ = (a ≫ e.hom) ≫ e.inv := congrArg (· ≫ e.inv) (he i).symm
      _ = a ≫ (e.hom ≫ e.inv) := Category.assoc a _ _
      _ = a := (congrArg (a ≫ ·) e.hom_inv_id).trans (Category.comp_id a)
  constructor
  · rintro ⟨h, hf, hg⟩
    have hb (i : Fin 2) (f₀ : F.obj X ⟶ Y)
        (hi : cylinderSection X (intervalEndpoint C i) ≫ h = adj.homEquiv X Y f₀) :
        cylinderSection (F.obj X) (intervalEndpoint C i) ≫ e.inv ≫ H.symm h = f₀ := by
      apply (adj.homEquiv X Y).injective
      calc
        _ = adj.homEquiv X Y (F.map (cylinderSection X (intervalEndpoint C i)) ≫ H.symm h) :=
          congrArg (adj.homEquiv X Y)
            ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ H.symm h) (hsection i)))
        _ = cylinderSection X (intervalEndpoint C i) ≫ H (H.symm h) :=
          adj.homEquiv_naturality_left _ _
        _ = _ := (congrArg (_ ≫ ·) (H.apply_symm_apply h)).trans hi
    exact ⟨e.inv ≫ H.symm h, hb 0 f hf, hb 1 g hg⟩
  · rintro ⟨h, hf, hg⟩
    have hb (i : Fin 2) (f₀ : F.obj X ⟶ Y)
        (hi : cylinderSection (F.obj X) (intervalEndpoint C i) ≫ h = f₀) :
        cylinderSection X (intervalEndpoint C i) ≫ H (e.hom ≫ h) =
          adj.homEquiv X Y f₀ := by
      calc
        _ = adj.homEquiv X Y (F.map (cylinderSection X (intervalEndpoint C i)) ≫ e.hom ≫ h) :=
          (adj.homEquiv_naturality_left _ _).symm
        _ = _ := congrArg (adj.homEquiv X Y)
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h) (he i)).trans hi))
    exact ⟨H (e.hom ≫ h), hb 0 f hf, hb 1 g hg⟩

end CategoryTheory.PointedSimplicialPresheaf

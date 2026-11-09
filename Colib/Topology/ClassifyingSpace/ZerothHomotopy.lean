/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ConnectedComponents

/-!
# Categorical components and path components of the original classifying space

The comparison sends an object component to the path component of its actual
nerve vertex. Its inverse uses the index of the existing component decomposition.
Both quotients are Mathlib's native objects.
-/

@[expose] public noncomputable section

universe u
namespace CategoryTheory

variable (C : Type u) [Category.{u} C]

/-- The actual vertex path-component functor to a discrete category. -/
def classifyingSpaceVertexComponents : C ⥤ Discrete (ZerothHomotopy (ClassifyingSpace C)) where
  obj c := Discrete.mk (ZerothHomotopy.mk (classifyingSpacePoint c))
  map f := Discrete.eqToHom (ZerothHomotopy.sound (classifyingSpacePath f))

/-- Categorical components map to the path components of their original vertices. -/
def classifyingSpaceComponentToZerothHomotopy :
    ConnectedComponents C → ZerothHomotopy (ClassifyingSpace C) :=
  ConnectedComponents.liftFunctor C (classifyingSpaceVertexComponents C)

/-- The categorical index of a point in the existing component decomposition. -/
def classifyingSpaceComponentIndex (x : ClassifyingSpace C) : ConnectedComponents C :=
  ((classifyingSpaceComponentSigmaHomeomorph C).symm x).1

/-- The index of an actual object vertex is its original categorical component. -/
@[simp] theorem classifyingSpaceComponentIndex_point (c : C) :
    classifyingSpaceComponentIndex C (classifyingSpacePoint c) = ConnectedComponents.mk c := by
  let v : (ConnectedComponents.mk c).Component := ⟨c, rfl⟩
  have h : classifyingSpaceComponentSigmaHomeomorph C
      ⟨ConnectedComponents.mk c, classifyingSpacePoint v⟩ = classifyingSpacePoint c := by
    simp only [classifyingSpaceComponentSigmaHomeomorph_apply, classifyingSpaceMap_point,
      ObjectProperty.ι_obj, v]
  change ((classifyingSpaceComponentSigmaHomeomorph C).symm _).1 = _
  rw [← h, Homeomorph.symm_apply_apply]

/-- An actual path cannot change the categorical index of the component decomposition. -/
theorem classifyingSpaceComponentIndex_eq_of_joined {x y : ClassifyingSpace C}
    (h : Joined x y) : classifyingSpaceComponentIndex C x = classifyingSpaceComponentIndex C y :=
  classifyingSpace_sigma_joined_index C _ _
    (h.map (classifyingSpaceComponentSigmaHomeomorph C).symm.continuous)

/-- The original classifying space has exactly the native categorical components. -/
def classifyingSpaceComponentsEquiv :
    ConnectedComponents C ≃ ZerothHomotopy (ClassifyingSpace C) where
  toFun := classifyingSpaceComponentToZerothHomotopy C
  invFun := ZerothHomotopy.lift (classifyingSpaceComponentIndex C)
    (fun {_ _} p ↦ classifyingSpaceComponentIndex_eq_of_joined C ⟨p⟩)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h c => exact classifyingSpaceComponentIndex_point C c
  right_inv x := by
    induction x using ZerothHomotopy.rec with
    | mk x =>
      obtain ⟨c, hc⟩ := classifyingSpace_joined_vertex x
      have hi := classifyingSpaceComponentIndex_eq_of_joined C hc
      rw [classifyingSpaceComponentIndex_point] at hi
      change classifyingSpaceComponentToZerothHomotopy C (classifyingSpaceComponentIndex C x) =
        ZerothHomotopy.mk x
      rw [← hi]
      exact Quotient.sound hc

/-- On object generators, the equivalence is the original vertex map. -/
@[simp] theorem classifyingSpaceComponentsEquiv_mk (c : C) :
    classifyingSpaceComponentsEquiv C (ConnectedComponents.mk c) =
      ZerothHomotopy.mk (classifyingSpacePoint c) := rfl

/-- The inverse at an original object vertex recovers the original categorical component. -/
@[simp] theorem classifyingSpaceComponentsEquiv_symm_mk (c : C) :
    (classifyingSpaceComponentsEquiv C).symm (ZerothHomotopy.mk (classifyingSpacePoint c)) =
      ConnectedComponents.mk c :=
  classifyingSpaceComponentIndex_point C c

variable {C} {D : Type u} [Category.{u} D]

/-- The comparison intertwines each actual nerve-realization map with its categorical map. -/
theorem classifyingSpaceComponentsEquiv_naturality (F : C ⥤ D) (x : ConnectedComponents C) :
    classifyingSpaceComponentsEquiv D (F.mapConnectedComponents x) =
      Quotient.map (classifyingSpaceMap F)
        (fun (x y : ClassifyingSpace C) (h : Joined x y) ↦
          h.map (classifyingSpaceMap F).hom.continuous)
        (classifyingSpaceComponentsEquiv C x) := by
  induction x using Quotient.inductionOn with
  | h c =>
    change ZerothHomotopy.mk (classifyingSpacePoint (F.obj c)) =
      ZerothHomotopy.mk (classifyingSpaceMap F (classifyingSpacePoint c))
    rw [classifyingSpaceMap_point]

end CategoryTheory

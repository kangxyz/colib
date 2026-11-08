/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.WeakObjectSimplex
public import Colib.CategoryTheory.Waldhausen.SConstruction.ObjectSimplex
public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinderNaturality


/-! # The original weak-object square as an actual nerve cylinder

The two constructions order a mixed map differently. Original row-transformation naturality
identifies them while retaining both independent simplex operators and the original arrow.
-/
/- Implementation provenance: selected declarations from
   `Quillen/Waldhausen/GrothendieckComparison/WeakObjectCylinder.lean`
   at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
   Original objects, maps, hypotheses and universe parameters are retained.
   Source-only preparation; native validation remains pending. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B : C} (f : A ⟶ B) (hf : W.weq f)

/-- The specified one-row transformation cylinder is exactly the original weak-arrow grid. -/
theorem weakObjectSimplex_cylinder {n : SimplexCategory}
    (α τ : n ⟶ ⦋1⦌) :
    nerveCylinderDiagram
        (whiskerLeft (intervalProjection n ⋙ indexMap α) ((oneEmbedding W).map f).hom) τ =
      gridMap₂ α τ ⋙ (W.weakObjectSimplex f hf).val := by
  let U : WeakRows W ⦋1⦌ ⥤ (Interval ⦋1⦌ ⥤ C) := {
    obj := fun X ↦ X.obj.obj
    map := fun g ↦ g.hom.hom
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }
  let J := intervalProjection n ⋙ indexMap α
  let K := ComposableArrows.mk₁ (W.oneWeakArrow f hf)
  have hK : ComposableArrows.mk₁ (whiskerLeft J ((oneEmbedding W).map f).hom) =
      K ⋙ U ⋙ (whiskeringLeft (Grid₂ n n) (Interval ⦋1⦌) C).obj J := by
    refine ComposableArrows.ext₁
      (F := ComposableArrows.mk₁ (whiskerLeft J ((oneEmbedding W).map f).hom))
      (G := K ⋙ U ⋙ (whiskeringLeft (Grid₂ n n) (Interval ⦋1⦌) C).obj J) rfl rfl ?_
    simp [K, U, oneWeakArrow]
  unfold nerveCylinderDiagram
  rw [hK]
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro p q a
  simpa only [Monotone.functor, U, J, K, nerveTimeFunctor, gridMap₂, intervalProjection, indexMap,
    Functor.comp_obj, Functor.prod'_obj, Functor.id_obj, Functor.id_map,
    whiskeringLeft_obj_obj, whiskerLeft_app,
    Functor.comp_map, Functor.uncurry_obj_map, Functor.prod'_map,
    whiskeringLeft_obj_map, whiskerLeft_app, weakObjectSimplex, weakChainToGrid_map,
    eqToHom_refl, Category.id_comp, Category.comp_id] using
    ((K.map (homOfLE (τ.toOrderHom.monotone (leOfHom a).1))).hom.hom.naturality
      (J.map a)).symm

end CategoryTheory.Waldhausen.Structure

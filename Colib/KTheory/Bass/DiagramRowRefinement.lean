/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramRowInterchange
public import Colib.Topology.Prespectrum.RowRefinementFunctoriality

/-!
# Actual row refinements of a row-natural spectrum diagram

A based row interchange that commutes with the original index arrows gives a diagram of
actual distinguished-row refinements. No Model or stability hypothesis is needed for this
functorial construction. Each arrow retains the original pointwise action at both zero-level
loop coordinates.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowRefinement
variable {C : Type u} [Category.{v} C] (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))

/-- The original index arrows act pointwise on their actual row refinements. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowRefinement.lean:32-62"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
def diagram : C ⥤ LoopPrespectrum.{w} where
  obj X := RowRefinement.spectrum (F.obj X) (q X) (hp X)
  map {X Y} g := RowRefinement.map (q X) (q Y) (hp X) (hp Y) (F.map g) (hn g)
  map_id X := by
    apply Hom.ext; funext n; apply ContinuousMap.ext; intro γ
    cases n with
    | zero =>
      change Path (Path.refl ((F.obj _).point 2)) (Path.refl ((F.obj _).point 2)) at γ
      apply Path.ext; funext r; apply Path.ext; funext s
      exact congrArg (fun a => a.map 2 (γ r s)) (F.map_id X)
    | succ k =>
      change Path ((F.obj _).point (k + 2)) ((F.obj _).point (k + 2)) at γ
      apply Path.ext; funext s
      exact congrArg (fun a => a.map (k + 2) (γ s)) (F.map_id X)
  map_comp f g := by
    apply Hom.ext; funext n; apply ContinuousMap.ext; intro γ
    cases n with
    | zero =>
      change Path (Path.refl ((F.obj _).point 2)) (Path.refl ((F.obj _).point 2)) at γ
      apply Path.ext; funext r; apply Path.ext; funext s
      exact congrArg (fun a => a.map 2 (γ r s)) (F.map_comp f g)
    | succ k =>
      change Path ((F.obj _).point (k + 2)) ((F.obj _).point (k + 2)) at γ
      apply Path.ext; funext s
      exact congrArg (fun a => a.map (k + 2) (γ s)) (F.map_comp f g)

variable (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
  q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
    (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)

/-- The actual two-structure equation supplies the whole original comparison transformation. -/
@[colib_tag "COL-0519", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowRefinement.lean:63-67"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
def comparison : F ⟶ diagram F q hp hn where
  app X := RowRefinement.comparison (F.obj X) (q X) (hp X) (hs X)
  naturality {X Y} g := RowRefinement.comparison_naturality (q X) (q Y) (hp X) (hp Y)
    (F.map g) (hn g) (hs X) (hs Y)

end KTheory.Bass.DiagramRowRefinement

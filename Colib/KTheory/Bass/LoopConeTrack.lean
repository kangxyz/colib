/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.ConeTrack
public import Colib.KTheory.Bass.LoopStrength

/-! # Evaluation through the original induced cone action and inverse index map -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u v w
namespace KTheory.Bass.LoopConeTrack
open ConeTrack LoopStrength
variable {C : Type u} [Category.{v} C]

/-- The existing cone map retains composition of actual diagram transformations. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopConeTrack.lean:24-36"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem coneMap_comp (Q : C ⥤ Arrow (Arrow C))
    {E F G : C ⥤ LoopPrespectrum.{w}} (η : E ⟶ F) (θ : F ⟶ G) :
    map Q (η ≫ θ) = map Q η ≫ map Q θ := by
  apply NatTrans.ext
  funext X
  change (strictSquareComparisonFunctor ⋙ mappingConeFunctor).map
    (diagramSquareMap (η ≫ θ) (Q.obj X)) = _
  have h : diagramSquareMap (η ≫ θ) (Q.obj X) =
      diagramSquareMap η (Q.obj X) ≫ diagramSquareMap θ (Q.obj X) := rfl
  rw [h, Functor.map_comp]
  rfl

/-- The complete inverse index map is natural in an arbitrary diagram transformation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopConeTrack.lean:37-49"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem indexMap_naturality (Q : C ⥤ Arrow (Arrow C)) (L : C ⥤ C)
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    {E F : C ⥤ LoopPrespectrum.{w}} (η : E ⟶ F) (X : C) :
    (map Q (Functor.whiskerLeft L η)).app X ≫ (indexMap Q L χ F).app X =
      (indexMap Q L χ E).app X ≫ (map Q η).app (L.obj X) := by
  let T := (Functor.mapArrowFunctor (Arrow C) (Arrow LoopPrespectrum.{w})).map
    ((Functor.mapArrowFunctor C LoopPrespectrum.{w}).map η)
  have h := congrArg (strictSquareComparisonFunctor ⋙ mappingConeFunctor).map
    (T.naturality (χ.inv.app X))
  simp only [Functor.map_comp] at h
  exact h.symm

/-- The original evaluation map at a fixed independent loop coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopConeTrack.lean:50-68"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
def evaluationAt (F : C ⥤ LoopPrespectrum.{w}) (t : unitInterval) :
    F ⋙ parameterLoopingFunctor ⟶ F :=
  diagramHomotopyAt (η := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
    (θ := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
    (evaluation F) (evaluation_naturality F) t

variable (Q : C ⥤ Arrow (Arrow C)) (L : C ⥤ C) (c : 𝟭 C ⟶ L)
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))
    (F : C ⥤ LoopPrespectrum.{w})
    (H : ∀ X, Homotopy (F.map (c.app X)) (F.map (c.app X)))
    (hH : ∀ {X Y} (g : X ⟶ Y) n r x,
      (F.map (L.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

include hH in
/-- Pointwise looping keeps coefficient naturality at every original track time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopConeTrack.lean:69-78"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem loop_naturality {X Y : C} (g : X ⟶ Y) n r x :
    ((F ⋙ parameterLoopingFunctor).map (L.map g)).map n
        (((H X).parameterLooping).level n (r, x)) =
      ((H Y).parameterLooping).level n
        (r, ((F ⋙ parameterLoopingFunctor).map g).map n x) := by
  apply Path.ext
  funext t
  exact hH g n r (Path.toContinuousMap x t)

/-- Evaluation intertwines the original time slices before applying the cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopConeTrack.lean:79-95"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem evaluation_timeSlice (r t : unitInterval) :
    evaluationAt F t ≫ diagramHomotopyAt
      (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F) H hH r =
      diagramHomotopyAt
        (η := Functor.whiskerRight c (F ⋙ parameterLoopingFunctor))
        (θ := Functor.whiskerRight c (F ⋙ parameterLoopingFunctor))
        (fun X => (H X).parameterLooping)
        (loop_naturality L c F H hH) r ≫ Functor.whiskerLeft L (evaluationAt F t) := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

/-- The full inverse-indexed cone action commutes with evaluation, with both times free. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/LoopConeTrack.lean:96-106"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem action_evaluation (X : C) (r t : unitInterval) :
    (map Q (evaluationAt F t)).app X ≫ (action Q L c χ hχ F H hH X).at r =
      (action Q L c χ hχ (F ⋙ parameterLoopingFunctor)
        (fun Y => (H Y).parameterLooping) (loop_naturality L c F H hH) X).at r ≫
          (map Q (evaluationAt F t)).app (L.obj X) := by
  refine (congrArg (fun a => (map Q (evaluationAt F t)).app X ≫ a)
    (action_at Q L c χ hχ F H hH X r)).trans ?_
  refine Eq.trans ?_ (congrArg (fun a => a ≫ (map Q (evaluationAt F t)).app (L.obj X))
    (action_at Q L c χ hχ (F ⋙ parameterLoopingFunctor)
      (fun Y => (H Y).parameterLooping) (loop_naturality L c F H hH) X r).symm)
  have h := congrArg (fun η => (map Q η).app X) (evaluation_timeSlice L c F H hH r t)
  simp only [coneMap_comp, NatTrans.comp_app] at h
  simp only [NatTrans.comp_app]
  rw [← Category.assoc, h, Category.assoc, indexMap_naturality, ← Category.assoc]

end KTheory.Bass.LoopConeTrack

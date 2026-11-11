/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ConeTrack

/-!
# The whole unit square of the induced cone track

The derived cone action uses the inverse index interchange. Postcomposing by the
original forward interchange therefore recovers the Bass image of the original
track at every time. Parameter looping retains the independent input-loop time.
This proves the finite whole-unit square for the specified induced action; it
assumes neither two-time scalar interchange nor equality with another chosen action.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u v w
namespace KTheory.Bass.ConeTrack
variable {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) (L : C ⥤ C) (c : 𝟭 C ⟶ L)
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))
    (F : C ⥤ LoopPrespectrum.{w})
    (H : ∀ X, Homotopy (F.map (c.app X)) (F.map (c.app X)))
    (hH : ∀ {X Y} (g : X ⟶ Y) n r x,
      (F.map (L.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

/-- The specified inverse cone-index map cancels the original forward index map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrackUnitSquare.lean:38"
  "adaptation" "Original actual geometric seed cospan and whole unit square."]
theorem action_index (X : C) (r : unitInterval) :
    (action Q L c χ hχ F H hH X).at r ≫
        (F.mapArrow.mapArrow ⋙ strictSquareComparisonFunctor ⋙ mappingConeFunctor).map
          (χ.hom.app X) =
      (map Q (diagramHomotopyAt
        (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F) H hH r)).app X := by
  let K := F.mapArrow.mapArrow ⋙ strictSquareComparisonFunctor ⋙ mappingConeFunctor
  have hc : K.map (χ.inv.app X) ≫ K.map (χ.hom.app X) = 𝟙 _ := by
    rw [← K.map_comp]
    simp
  rw [action_at]
  change (_ ≫ K.map (χ.inv.app X)) ≫ K.map (χ.hom.app X) = _
  let m := (map Q (diagramHomotopyAt
    (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F) H hH r)).app X
  exact (Category.assoc m (K.map (χ.inv.app X)) (K.map (χ.hom.app X))).trans
    ((congrArg (fun k => m ≫ k) hc).trans (Category.comp_id m))

/-- The induced looped cone track satisfies the original whole unit square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrackUnitSquare.lean:56"
  "adaptation" "Original actual geometric seed cospan and whole unit square."]
theorem looped_action_index (X : C) (r : unitInterval) :
    (action Q L c χ hχ F H hH X).parameterLooping.at r ≫
        strictSquareLoopedConeFunctor.map (F.mapArrow.mapArrow.map (χ.hom.app X)) =
      (strictDiagramMapHomotopy
        (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F)
        H hH Q X).at r := by
  rw [Homotopy.parameterLooping_at, strictDiagramMapHomotopy_at]
  change parameterLoopingFunctor.map ((action Q L c χ hχ F H hH X).at r) ≫
      parameterLoopingFunctor.map
        ((F.mapArrow.mapArrow ⋙ strictSquareComparisonFunctor ⋙ mappingConeFunctor).map
          (χ.hom.app X)) =
    parameterLoopingFunctor.map
      ((map Q (diagramHomotopyAt
        (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F) H hH r)).app X)
  have hm := congrArg parameterLoopingFunctor.map
    (action_index Q L c χ hχ F H hH X r)
  exact (parameterLoopingFunctor.map_comp ((action Q L c χ hχ F H hH X).at r)
    ((F.mapArrow.mapArrow ⋙ strictSquareComparisonFunctor ⋙ mappingConeFunctor).map
      (χ.hom.app X))).symm.trans hm

/-- Both the original action time and the independent input-loop time remain unchanged. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrackUnitSquare.lean:77"
  "adaptation" "Original actual geometric seed cospan and whole unit square."]
theorem looped_action_index_apply (X : C) (n : ℕ) (r t : unitInterval)
    (γ : Path (((diagram Q F).obj X).point n) (((diagram Q F).obj X).point n)) :
    Path.toContinuousMap
      ((strictSquareLoopedConeFunctor.map (F.mapArrow.mapArrow.map (χ.hom.app X))).map n
        ((action Q L c χ hχ F H hH X).parameterLooping.level n (r, γ))) t =
      (diagramSquareMapHomotopy
        (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F)
        H hH (Q.obj X)).cone.level n (r, γ t) :=
  congrArg (fun f => Path.toContinuousMap (f.map n γ) t)
    (looped_action_index Q L c χ hχ F H hH X r)

end KTheory.Bass.ConeTrack

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.LoopConeTrack

/-! # Finite preservation of whole track intertwiners by the original cone and loop -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u v w
namespace KTheory.Bass.ConeTrackEquivariance
open ConeTrack LoopConeTrack
variable {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) (L : C ⥤ C) (c : 𝟭 C ⟶ L)
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))
    {F G : C ⥤ LoopPrespectrum.{w}}
    (HF : ∀ X, Homotopy (F.map (c.app X)) (F.map (c.app X)))
    (HG : ∀ X, Homotopy (G.map (c.app X)) (G.map (c.app X)))
    (hF : ∀ {X Y} (g : X ⟶ Y) n r x,
      (F.map (L.map g)).map n ((HF X).level n (r, x)) =
        (HF Y).level n (r, (F.map g).map n x))
    (hG : ∀ {X Y} (g : X ⟶ Y) n r x,
      (G.map (L.map g)).map n ((HG X).level n (r, x)) =
        (HG Y).level n (r, (G.map g).map n x))
    (η : F ⟶ G)
    (hη : ∀ X r, η.app X ≫ (HG X).at r = (HF X).at r ≫ η.app (L.obj X))

include hη in
/-- The input whole-value squares give equality of the actual natural time slices. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrackEquivariance.lean:40-51"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem timeSlice_square (r : unitInterval) :
    η ≫ diagramHomotopyAt
      (η := Functor.whiskerRight c G) (θ := Functor.whiskerRight c G) HG hG r =
    diagramHomotopyAt
      (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F) HF hF r ≫
        Functor.whiskerLeft L η := by
  apply NatTrans.ext
  funext X
  exact hη X r

include hη in
/-- Cone induction retains the complete original inverse index interchange. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrackEquivariance.lean:52-63"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem cone_action (X : C) (r : unitInterval) :
    (map Q η).app X ≫ (action Q L c χ hχ G HG hG X).at r =
      (action Q L c χ hχ F HF hF X).at r ≫ (map Q η).app (L.obj X) := by
  rw [action_at, action_at]
  have h := congrArg (fun θ => (map Q θ).app X)
    (timeSlice_square L c HF HG hF hG η hη r)
  simp only [coneMap_comp, NatTrans.comp_app] at h
  simp only [NatTrans.comp_app]
  rw [← Category.assoc, h, Category.assoc, indexMap_naturality, ← Category.assoc]

include hη in
/-- Loop induction preserves the same track time and the independent input-loop time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrackEquivariance.lean:64-72"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem loop_action (X : C) (r : unitInterval) :
    parameterLoopingMap (η.app X) ≫ (HG X).parameterLooping.at r =
      (HF X).parameterLooping.at r ≫ parameterLoopingMap (η.app (L.obj X)) := by
  rw [Homotopy.parameterLooping_at, Homotopy.parameterLooping_at]
  exact (parameterLoopingFunctor.map_comp _ _).symm.trans
    ((congrArg parameterLoopingFunctor.map (hη X r)).trans
      (parameterLoopingFunctor.map_comp _ _))

/-- The cone image of any original transformation preserves the entire specified source null. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrackEquivariance.lean:73-80"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem cone_sourceNull (X : C) (n : ℕ) (s : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space n) :
    ((map Q η).app X).map n
        ((StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X))).level n (s, x)) =
      (StrictSquare.sourceNullHomotopy (G.mapArrow.mapArrow.obj (Q.obj X))).level n
        (s, (η.app (Q.obj X).left.left).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply (diagramSquareMap η (Q.obj X)) n s x

end KTheory.Bass.ConeTrackEquivariance

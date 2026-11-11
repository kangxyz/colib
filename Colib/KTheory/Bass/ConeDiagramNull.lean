/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.ConeTrack
public import Colib.Topology.Prespectrum.DiagramNullHomotopy

/-! # The original unlooped cone action on whole diagram nullhomotopies -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.ConeTrack
variable {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) {F G K : C ⥤ LoopPrespectrum.{w}}

/-- The original unlooped diagram map preserves literal composition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeDiagramNull.lean:23"
  "adaptation" "Original whole cone null, fixed time and endpoint casts."]
theorem map_comp (a : F ⟶ G) (b : G ⟶ K) :
    map Q (a ≫ b) = map Q a ≫ map Q b := by
  unfold map
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    Functor.whiskerRight_comp, Functor.whiskerLeft_comp]

/-- The cone's two quotient cells send the original zero square to the original zero map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeDiagramNull.lean:30"
  "adaptation" "Original whole cone null, fixed time and endpoint casts."]
theorem map_zero_app (X : C) :
    (map Q (diagramZeroMap F G)).app X =
      zeroHom ((diagram Q F).obj X) ((diagram Q G).obj X) := by
  let T := G.mapArrow.mapArrow.obj (Q.obj X)
  let a := diagramSquareMap (diagramZeroMap F G) (Q.obj X)
  have hs := StrictSquare.spanMap_eq_zero a rfl rfl rfl
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  change (mappingConeMap (strictSquareComparisonFunctor.map a)).map n x =
    (mappingCone (StrictSquare.comparison T)).point n
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl y => rfl
    | inr z =>
      change ReducedMappingCone.cylinder ((StrictSquare.span T).point n) (T.right.right.point n)
        ((StrictSquare.comparison T).map n) (z.1, (StrictSquare.spanMap a).map n z.2) = _
      rw [hs]
      exact ReducedMappingCone.cylinder_base ((StrictSquare.span T).point n)
        (T.right.right.point n) ((StrictSquare.comparison T).map n) z.1

variable {a b : F ⟶ G} (H : ∀ X, Homotopy (a.app X) (b.app X))
    (hH : ∀ {X Y} (f : X ⟶ Y) n r x,
      (G.map f).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map f).map n x))

/-- Use the original four-corner whole homotopy on the actual unlooped cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeDiagramNull.lean:58"
  "adaptation" "Original whole cone null, fixed time and endpoint casts."]
def mapHomotopy (X : C) : Homotopy ((map Q a).app X) ((map Q b).app X) :=
  (diagramSquareMapHomotopy H hH (Q.obj X)).cone

/-- Every cone-homotopy time slice is the original cone image of the same input time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeDiagramNull.lean:62"
  "adaptation" "Original whole cone null, fixed time and endpoint casts."]
theorem mapHomotopy_at (X : C) (r : unitInterval) :
    (mapHomotopy Q H hH X).at r = (map Q (diagramHomotopyAt H hH r)).app X := by
  change (diagramSquareMapHomotopy H hH (Q.obj X)).cone.at r = _
  rw [StrictSquare.MapHomotopy.cone_at, diagramSquareMapHomotopy_at]
  rfl

/-- The entire original cone homotopy is natural at the unchanged time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeDiagramNull.lean:69"
  "adaptation" "Original whole cone null, fixed time and endpoint casts."]
theorem mapHomotopy_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : ((diagram Q F).obj X).space n) :
    ((diagram Q G).map f).map n ((mapHomotopy Q H hH X).level n (r, x)) =
      (mapHomotopy Q H hH Y).level n (r, ((diagram Q F).map f).map n x) := by
  change ((mapHomotopy Q H hH X).at r ≫ (diagram Q G).map f).map n x =
    ((diagram Q F).map f ≫ (mapHomotopy Q H hH Y).at r).map n x
  rw [mapHomotopy_at, mapHomotopy_at]
  exact congrArg (fun k => k.map n x) ((map Q (diagramHomotopyAt H hH r)).naturality f).symm

/-- The selected original null is sent through the original cone, with only endpoint casts. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeDiagramNull.lean:79"
  "adaptation" "Original whole cone null, fixed time and endpoint casts."]
def diagramNull {a : F ⟶ G} {b : G ⟶ K} (N : DiagramNullHomotopy a b) :
    DiagramNullHomotopy (map Q a) (map Q b) where
  homotopy X := (mapHomotopy Q (a := a ≫ b) (b := diagramZeroMap F K)
    N.homotopy N.naturality X).cast
    (congrArg (fun η => η.app X) (map_comp Q a b)) (map_zero_app Q X)
  naturality f n r x := mapHomotopy_naturality Q
    (a := a ≫ b) (b := diagramZeroMap F K) N.homotopy N.naturality f n r x

/-- Casting the two endpoints changes no value of the complete original null. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeDiagramNull.lean:88"
  "adaptation" "Original whole cone null, fixed time and endpoint casts."]
theorem diagramNull_at {a : F ⟶ G} {b : G ⟶ K} (N : DiagramNullHomotopy a b)
    (X : C) (r : unitInterval) :
    ((diagramNull Q N).homotopy X).at r =
      (map Q (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r)).app X :=
  mapHomotopy_at Q (a := a ≫ b) (b := diagramZeroMap F K) N.homotopy N.naturality X r

end KTheory.Bass.ConeTrack

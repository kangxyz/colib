/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.StrictDiagramIterateNull
public import Colib.KTheory.Bass.StrictDiagramMap

/-!
# The original iterated null tracks at every actual time

Each time slice of the recursively specified null track is the unchanged Bass iterate of the
original time-slice natural transformation. The proof uses exactly the accepted successor
transport maps. A proved original whole seed square therefore propagates to every actual
finite transition without a new track or a second geometric induction.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F G K : C ⥤ LoopPrespectrum.{w}} {a : F ⟶ G} {b : G ⟶ K}
    (H : DiagramNullHomotopy a b)

/-- The entire original time-slice transformation is retained by every unchanged Bass iterate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIterateNullTimeSlice.lean:29"
  "adaptation" "Original successor transports and same-time iterated null."]
theorem strictDiagramIterateNull_timeSlice (n : ℕ) (r : unitInterval) :
    diagramHomotopyAt
      (η := (strictDiagramIterate Q n).map a ≫ (strictDiagramIterate Q n).map b)
      (θ := diagramZeroMap ((strictDiagramIterate Q n).obj F) ((strictDiagramIterate Q n).obj K))
      (strictDiagramIterateNull Q H n).homotopy (strictDiagramIterateNull Q H n).naturality r =
    (strictDiagramIterate Q n).map
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K) H.homotopy H.naturality r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let h := diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
      H.homotopy H.naturality r
    have ht : strictDiagramSuccessorMap Q F n ≫
        (strictDiagramFunctor Q).map ((strictDiagramIterate Q n).map h) ≫
          inv (strictDiagramSuccessorMap Q K n) = (strictDiagramIterate Q (n + 1)).map h := by
      rw [← Category.assoc, ← strictDiagramSuccessorMap_naturality Q h n, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    apply NatTrans.ext
    funext X
    apply Hom.ext
    funext m
    apply ContinuousMap.ext
    intro x
    change ((strictDiagramIterateNull Q H (n + 1)).homotopy X).level m (r, x) = _
    rw [strictDiagramIterateNull_succ_level]
    change ((inv (strictDiagramSuccessorMap Q K n)).app X).map m
      (((strictDiagramMapHomotopy
        (η := (strictDiagramIterate Q n).map a ≫ (strictDiagramIterate Q n).map b)
        (θ := diagramZeroMap ((strictDiagramIterate Q n).obj F) ((strictDiagramIterate Q n).obj K))
        (strictDiagramIterateNull Q H n).homotopy (strictDiagramIterateNull Q H n).naturality
        Q X).at r).map m (((strictDiagramSuccessorMap Q F n).app X).map m x)) = _
    have hs := strictDiagramMapHomotopy_at
      (η := (strictDiagramIterate Q n).map a ≫ (strictDiagramIterate Q n).map b)
      (θ := diagramZeroMap ((strictDiagramIterate Q n).obj F) ((strictDiagramIterate Q n).obj K))
      (strictDiagramIterateNull Q H n).homotopy (strictDiagramIterateNull Q H n).naturality Q X r
    have hs' := hs.trans (congrArg (fun f ↦ ((strictDiagramFunctor Q).map f).app X) ih)
    exact (congrArg (fun f ↦ ((inv (strictDiagramSuccessorMap Q K n)).app X).map m
      (f.map m (((strictDiagramSuccessorMap Q F n).app X).map m x))) hs').trans
        (congrArg (fun f ↦ (f.app X).map m x) ht)

/-- Every original prespectrum time slice is the corresponding actual iterated component map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIterateNullTimeSlice.lean:70"
  "adaptation" "Original successor transports and same-time iterated null."]
theorem strictDiagramIterateNull_at (n : ℕ) (X : C) (r : unitInterval) :
    ((strictDiagramIterateNull Q H n).homotopy X).at r =
      ((strictDiagramIterate Q n).map
        (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
          H.homotopy H.naturality r)).app X :=
  congrArg (fun f ↦ f.app X) (strictDiagramIterateNull_timeSlice Q H n r)

/-- The same identity retains every original level value, including degree-zero loops. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIterateNullTimeSlice.lean:78"
  "adaptation" "Original successor transports and same-time iterated null."]
theorem strictDiagramIterateNull_level (n : ℕ) (X : C) (m : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q n).obj F).obj X).space m) :
    ((strictDiagramIterateNull Q H n).homotopy X).level m (r, x) =
      (((strictDiagramIterate Q n).map
        (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
          H.homotopy H.naturality r)).app X).map m x :=
  congrArg (fun f ↦ f.map m x) (strictDiagramIterateNull_at Q H n X r)

/-- A proved original whole seed square propagates to the same actual finite transitions. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIterateNullTimeSlice.lean:87"
  "adaptation" "Original successor transports and same-time iterated null."]
theorem strictDiagramIterateNull_transition
    (σ : F ⟶ (strictDiagramFunctor Q).obj F)
    (τ : K ⟶ (strictDiagramFunctor Q).obj K)
    (hseed : ∀ r, σ ≫ (strictDiagramFunctor Q).map
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K) H.homotopy H.naturality r) =
      diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K) H.homotopy H.naturality r ≫ τ)
    (n : ℕ) (X : C) (m : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q n).obj F).obj X).space m) :
    ((strictDiagramIterateNull Q H (n + 1)).homotopy X).level m
        (r, ((strictDiagramTransition Q σ n).app X).map m x) =
      ((strictDiagramTransition Q τ n).app X).map m
        (((strictDiagramIterateNull Q H n).homotopy X).level m (r, x)) := by
  rw [strictDiagramIterateNull_level, strictDiagramIterateNull_level]
  exact congrArg (fun f ↦ (f.app X).map m x)
    (strictDiagramTransition_map Q σ τ _ (hseed r) n)

end KTheory.Bass

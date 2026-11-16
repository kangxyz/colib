/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

module

public import Colib.Topology.HELP.Nullhomotopic
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.LocallyFinite

/-!
# Filling a cube with prescribed coordinate faces in a contractible space

The edge identities are sufficient to paste the entire boundary, since opposite faces
are disjoint. The homotopy extension property of the literal boundary inclusion then
fills that same boundary, without reparametrizing any face.

Adapted from the boundary pasting and extension in
`Quillen/Topology/Realization/SimplexCubeFaces.lean` and
`Quillen/Waldhausen/SConstruction/Iterated/CommonReferenceNerveCubeExtension.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open scoped Topology unitInterval

namespace Topology.CubicalTests

universe u

/-- Boolean orientation of a coordinate face. -/
def faceEndpoint (b : Bool) : I := if b then 1 else 0

/-- A coordinate face inside the literal cube boundary, without universe lifts. -/
def coordinateFace {n : ℕ} (a : Fin n × Bool) :
    Set {x : Fin n → I // x ∈ Cube.boundary (Fin n)} :=
  {x | x.val a.1 = faceEndpoint a.2}

private theorem isClosed_coordinateFace {n : ℕ} (a : Fin n × Bool) :
    IsClosed (coordinateFace a) :=
  isClosed_eq ((continuous_apply a.1).comp continuous_subtype_val) continuous_const

private theorem coordinateFace_cover (n : ℕ) :
    ⋃ a : Fin n × Bool, coordinateFace a = Set.univ := by
  apply Set.iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨i, hi | hi⟩ := x.property
  · exact ⟨(i, false), hi⟩
  · exact ⟨(i, true), hi⟩

variable {Y : Type u} [TopologicalSpace Y] {n : ℕ}

/-- Agreement on the intersections of distinct axes, with each pair of axes used once. -/
def CoordinateFaceCompatible (F : ∀ a : Fin n × Bool, coordinateFace a → Y) : Prop :=
  ∀ (i j : Fin n), i < j → ∀ (b c : Bool) (x : {x : Fin n → I // x ∈ Cube.boundary (Fin n)})
    (hi : x ∈ coordinateFace (i, b)) (hj : x ∈ coordinateFace (j, c)),
    F (i, b) ⟨x, hi⟩ = F (j, c) ⟨x, hj⟩

private theorem coordinateFaceCompatible_pairwise
    (F : ∀ a : Fin n × Bool, coordinateFace a → Y) (hF : CoordinateFaceCompatible F)
    (a b : Fin n × Bool) (x : {x : Fin n → I // x ∈ Cube.boundary (Fin n)})
    (ha : x ∈ coordinateFace a) (hb : x ∈ coordinateFace b) :
    F a ⟨x, ha⟩ = F b ⟨x, hb⟩ := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rcases lt_trichotomy i j with h | h | h
  · exact hF i j h a b x ha hb
  · subst j
    cases a <;> cases b
    · rfl
    · exact (zero_ne_one (ha.symm.trans hb : (0 : I) = 1)).elim
    · exact (one_ne_zero (ha.symm.trans hb : (1 : I) = 0)).elim
    · rfl
  · exact (hF j i h b a x hb ha).symm

/-- The continuous intrinsic boundary map defined by whole-face maps agreeing on edges. -/
def glueCoordinateFaces (F : ∀ a : Fin n × Bool, C(coordinateFace a, Y))
    (hF : CoordinateFaceCompatible (fun a ↦ F a)) :
    C({x : Fin n → I // x ∈ Cube.boundary (Fin n)}, Y) :=
  ⟨Set.liftCover coordinateFace (fun a ↦ F a)
      (coordinateFaceCompatible_pairwise _ hF) (coordinateFace_cover n),
    (locallyFinite_of_finite coordinateFace).continuous (coordinateFace_cover n)
      isClosed_coordinateFace fun a ↦ by
        rw [continuousOn_iff_continuous_domRestrict]
        simpa +unfoldPartialApp only [Set.domRestrict, Set.liftCover_coe] using (F a).continuous⟩

/-- The pasted boundary agrees with the original face at every point of that face. -/
@[simp] theorem glueCoordinateFaces_apply
    (F : ∀ a : Fin n × Bool, C(coordinateFace a, Y))
    (hF : CoordinateFaceCompatible (fun a ↦ F a)) (a : Fin n × Bool) (x : coordinateFace a) :
    glueCoordinateFaces F hF x.val = F a x :=
  Set.liftCover_coe (S := coordinateFace) (f := fun a ↦ F a)
    (hf := coordinateFaceCompatible_pairwise _ hF) (hS := coordinateFace_cover n) x

/-- Compatible prescribed faces in a contractible target extend without changing the boundary. -/
theorem exists_fillCoordinateFaces [ContractibleSpace Y]
    (F : ∀ a : Fin n × Bool, C(coordinateFace a, Y))
    (hF : CoordinateFaceCompatible (fun a ↦ F a)) :
    ∃ E : C(Fin n → I, Y), ∀ (a : Fin n × Bool) (x : coordinateFace a), E x.val.val = F a x := by
  let b := glueCoordinateFaces F hF
  let b' : C(boundary.{u} n, Y) :=
    b.comp ⟨boundaryULiftHomeomorph n, (boundaryULiftHomeomorph n).continuous⟩
  obtain ⟨y, ⟨H⟩⟩ :=
    (contractible_iff_id_nullhomotopic Y).mp (inferInstance : ContractibleSpace Y)
  have hb : b'.Nullhomotopic := ⟨y, ⟨H.compContinuousMap b'⟩⟩
  obtain ⟨E, hE⟩ := exists_extend_of_nullhomotopic (boundaryInclusion n)
    (boundaryInclusion_hep n) b' hb
  refine ⟨E.comp ⟨ULift.up, continuous_uliftUp⟩, fun a x ↦ ?_⟩
  have he : E ⟨x.val.val⟩ = b x.val :=
    DFunLike.congr_fun hE ⟨⟨x.val.val⟩, x.val.property⟩
  exact he.trans (glueCoordinateFaces_apply F hF a x)

end Topology.CubicalTests

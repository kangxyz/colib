/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.Topology.Realization.SimplexCubeExtension
public import Mathlib.Topology.LocallyFinite

/-!
# Exact gluing and extension of six compatible whole simplex faces

The twelve coordinate-edge identities suffice to glue the six continuous closed-face maps.
The cube extension then agrees with every face at every point.

Adapted from `Quillen/Topology/Realization/SimplexCubeFaces.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open Convexity
open scoped Topology unitInterval

namespace Topology.SimplexCubeExtension

variable {X Y α : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite α]

/-- Finite closed-cover pasting, with exact equality on every member of the cover. -/
def glueClosedCover (S : α → Set X) (hS : ∀ a, IsClosed (S a))
    (hcover : ⋃ a, S a = Set.univ) (F : ∀ a, C(S a, Y))
    (hcompat : ∀ a b x (ha : x ∈ S a) (hb : x ∈ S b),
      F a ⟨x, ha⟩ = F b ⟨x, hb⟩) : C(X, Y) :=
  ⟨Set.liftCover S (fun a ↦ F a) hcompat hcover,
    (locallyFinite_of_finite S).continuous hcover hS fun a ↦ by
      rw [continuousOn_iff_continuous_domRestrict]
      simpa +unfoldPartialApp only [Set.domRestrict, Set.liftCover_coe]
        using (F a).continuous⟩

@[simp] theorem glueClosedCover_apply (S : α → Set X) (hS : ∀ a, IsClosed (S a))
    (hcover : ⋃ a, S a = Set.univ) (F : ∀ a, C(S a, Y))
    (hcompat : ∀ a b x (ha : x ∈ S a) (hb : x ∈ S b),
      F a ⟨x, ha⟩ = F b ⟨x, hb⟩) (a : α) (x : S a) :
    glueClosedCover S hS hcover F hcompat x = F a x :=
  Set.liftCover_coe (S := S) (f := fun a ↦ F a) (hf := hcompat) (hS := hcover) x

/-- The two endpoint values used to index the six faces. -/
def endpoint (b : Bool) : I := if b then 1 else 0

/-- A coordinate face, regarded as a closed subset of the whole cube boundary. -/
def face (a : Fin 3 × Bool) : Set boundary := {x | x.val a.1 = endpoint a.2}

theorem isClosed_face (a : Fin 3 × Bool) : IsClosed (face a) :=
  isClosed_eq ((continuous_apply a.1).comp continuous_subtype_val) continuous_const

theorem faces_cover : ⋃ a : Fin 3 × Bool, face a = Set.univ := by
  apply Set.iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨i, hi | hi⟩ := x.property
  · exact ⟨(i, false), hi⟩
  · exact ⟨(i, true), hi⟩

/-- One identity on each whole geometric edge: three increasing coordinate pairs and four
endpoint pairs. Thus the interface contains exactly the twelve nontrivial intersections. -/
def EdgeCompatible {Z : Type*} (F : ∀ a : Fin 3 × Bool, face a → Z) : Prop :=
  ∀ (i j : Fin 3), i < j → ∀ (a b : Bool) (x : boundary)
    (hi : x ∈ face (i, a)) (hj : x ∈ face (j, b)),
    F (i, a) ⟨x, hi⟩ = F (j, b) ⟨x, hj⟩

/-- Opposite faces have empty intersection; equal faces agree by proof irrelevance, so the
twelve edge identities give all pairwise intersection identities required for pasting. -/
theorem edgeCompatible_pairwise {Z : Type*} (F : ∀ a : Fin 3 × Bool, face a → Z)
    (hF : EdgeCompatible F) (a b : Fin 3 × Bool) (x : boundary)
    (ha : x ∈ face a) (hb : x ∈ face b) : F a ⟨x, ha⟩ = F b ⟨x, hb⟩ := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rcases lt_trichotomy i j with h | h | h
  · exact hF i j h a b x ha hb
  · subst j
    cases a <;> cases b
    · rfl
    · have h01 : (0 : I) = 1 := ha.symm.trans hb
      have hreal : (0 : ℝ) = 1 := congrArg (fun t : I ↦ (t : ℝ)) h01
      exact (zero_ne_one hreal).elim
    · have h10 : (1 : I) = 0 := ha.symm.trans hb
      have hreal : (1 : ℝ) = 0 := congrArg (fun t : I ↦ (t : ℝ)) h10
      exact (one_ne_zero hreal).elim
    · rfl
  · exact (hF j i h b a x hb ha).symm

/-- The glued continuous whole-boundary map, obtained solely from the face maps and their
twelve edge identities. -/
def gluedBoundary (N : ℕ) (F : ∀ a : Fin 3 × Bool, C(face a, StdSimplex ℝ (Fin (N + 1))))
    (hF : EdgeCompatible (fun a ↦ F a)) : C(boundary, StdSimplex ℝ (Fin (N + 1))) :=
  glueClosedCover face isClosed_face faces_cover F (edgeCompatible_pairwise (fun a ↦ F a) hF)

@[simp] theorem gluedBoundary_face (N : ℕ)
    (F : ∀ a : Fin 3 × Bool, C(face a, StdSimplex ℝ (Fin (N + 1))))
    (hF : EdgeCompatible (fun a ↦ F a)) (a : Fin 3 × Bool) (x : face a) :
    gluedBoundary N F hF x = F a x :=
  glueClosedCover_apply face isClosed_face faces_cover F
    (edgeCompatible_pairwise (fun a ↦ F a) hF) a x

/-- A continuous cube filler with all six specified whole faces unchanged. -/
def fillFaces (N : ℕ) (F : ∀ a : Fin 3 × Bool, C(face a, StdSimplex ℝ (Fin (N + 1))))
    (hF : EdgeCompatible (fun a ↦ F a)) : C(Cube, StdSimplex ℝ (Fin (N + 1))) :=
  cubeExtension N (gluedBoundary N F hF)

/-- Exact equality on each complete specified face; no face or speed is modified. -/
@[simp] theorem fillFaces_face (N : ℕ)
    (F : ∀ a : Fin 3 × Bool, C(face a, StdSimplex ℝ (Fin (N + 1))))
    (hF : EdgeCompatible (fun a ↦ F a)) (a : Fin 3 × Bool) (x : face a) :
    fillFaces N F hF x.val.val = F a x :=
  (cubeExtension_boundary N (gluedBoundary N F hF) x.val).trans
    (gluedBoundary_face N F hF a x)

end Topology.SimplexCubeExtension

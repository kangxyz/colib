/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.SignedPointControl

/-!
# Actual center control under signed native composition

The all-point incidence provenance gives two actual support points whose middle
projections agree. Consequently arbitrary designated target sets, and in
particular designated centers, compose for the genuine signed Tor pairing.

Adapted from `kangxyz/motivic` at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/PointControl.lean`,
blob `a406042039c0a29d86e865a2ec06b2214e3b4d66`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable [Smooth g] [Smooth h] [IsSeparated h]

/-- A surviving signed output support point comes from actual input support
points with exactly matching middle projection. -/
theorem exists_support_points_of_incidenceTorPairing_ne_zero
    (α : finiteCorrespondences f g) (β : finiteCorrespondences g h)
    (b : pullback (C := Scheme) f h)
    (hb : (incidenceTorPairing f g h α β).val b ≠ 0)
    (c : (integralComponentAt b).subscheme) :
    ∃ z : α.property.1.toFinset, ∃ w : β.property.1.toFinset,
      ∃ a : (integralComponentAt z.val).subscheme,
      ∃ d : (integralComponentAt w.val).subscheme,
        ((integralComponentAt z.val).subschemeι ≫ pullback.fst f g) a =
          ((integralComponentAt b).subschemeι ≫ pullback.fst f h) c ∧
        ((integralComponentAt z.val).subschemeι ≫ pullback.snd f g) a =
          ((integralComponentAt w.val).subschemeι ≫ pullback.fst g h) d ∧
        ((integralComponentAt w.val).subschemeι ≫ pullback.snd g h) d =
          ((integralComponentAt b).subschemeι ≫ pullback.snd f h) c := by
  obtain ⟨z, w, t, ht⟩ :=
    exists_incidence_point_of_incidenceTorPairing_ne_zero f g h α β b hb c
  let p := (integralComponentAt z.val).subschemeι ≫ pullback.snd f g
  let q := (integralComponentAt w.val).subschemeι ≫ pullback.fst g h
  refine ⟨z, w, pullback.fst p q t, pullback.snd p q t, ?_, ?_, ?_⟩
  · have he := congrArg (pullback.fst f h) ht
    change (correspondenceIncidenceMap f g h z.val w.val ≫ pullback.fst f h) t = _ at he
    rw [correspondenceIncidenceMap_fst] at he
    exact he
  · exact congrArg (fun r : correspondenceIncidence f g h z.val w.val ⟶ Y => r t)
      (pullback.condition (f := p) (g := q))
  · have he := congrArg (pullback.snd f h) ht
    change (correspondenceIncidenceMap f g h z.val w.val ≫ pullback.snd f h) t = _ at he
    rw [correspondenceIncidenceMap_snd] at he
    exact he

/-- Designated target sets compose for arbitrary signed native correspondences.
The control assumptions concern all actual support points, not just closed points. -/
theorem target_mem_of_incidenceTorPairing_ne_zero
    (α : finiteCorrespondences f g) (β : finiteCorrespondences g h)
    (x : X) (S : Set Y) (T : Set Z)
    (hS : ∀ z : α.property.1.toFinset, ∀ a : (integralComponentAt z.val).subscheme,
      ((integralComponentAt z.val).subschemeι ≫ pullback.fst f g) a = x →
      ((integralComponentAt z.val).subschemeι ≫ pullback.snd f g) a ∈ S)
    (hT : ∀ w : β.property.1.toFinset, ∀ d : (integralComponentAt w.val).subscheme,
      ((integralComponentAt w.val).subschemeι ≫ pullback.fst g h) d ∈ S →
      ((integralComponentAt w.val).subschemeι ≫ pullback.snd g h) d ∈ T)
    (b : pullback (C := Scheme) f h)
    (hb : (incidenceTorPairing f g h α β).val b ≠ 0)
    (c : (integralComponentAt b).subscheme)
    (hc : ((integralComponentAt b).subschemeι ≫ pullback.fst f h) c = x) :
    ((integralComponentAt b).subschemeι ≫ pullback.snd f h) c ∈ T := by
  obtain ⟨z, w, a, d, hs, hm, ht⟩ :=
    exists_support_points_of_incidenceTorPairing_ne_zero f g h α β b hb c
  exact ht ▸ hT w d (hm ▸ hS z a (hs.trans hc))

end Stacks.Chow

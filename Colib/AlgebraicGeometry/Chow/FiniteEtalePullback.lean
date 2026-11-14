/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Finite étale pullback and descent for native cycles

Finite étale pullback has multiplicity one at each point of the fibre. A
finitely supported cycle on the source of a finite étale surjection descends
if its pullbacks along the two projections of the actual fibre product
agree. This is the ambient-cycle descent used in Riou, *Opérations de
Steenrod motiviques*, arXiv:1207.3121v1, Definition 2.1.3, map (4).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Function

universe u v

namespace Stacks.Chow

variable {X Y : Scheme.{u}} {R : Type v} [AddCommMonoid R]

/-- Finite étale pullback copies each coefficient to every point of its fibre. -/
def finiteEtaleCyclePullback (f : X ⟶ Y) [IsFinite f] [Etale f] :
    AlgebraicCycle Y R →+ AlgebraicCycle X R where
  toFun c :=
    { toFun := fun x ↦ c (f x)
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := fun x _ ↦ by
        obtain ⟨U, hU, hfin⟩ := c.locallyFiniteSupport (f x)
        refine ⟨f ⁻¹' U, f.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
        exact f.finite_preimage hfin }
  map_zero' := by ext x; rfl
  map_add' _ _ := by ext x; rfl

@[simp]
theorem finiteEtaleCyclePullback_apply (f : X ⟶ Y) [IsFinite f] [Etale f]
    (c : AlgebraicCycle Y R) (x : X) :
    finiteEtaleCyclePullback f c x = c (f x) := rfl

/-- Finite étale pullback preserves finite point support. -/
theorem finiteEtaleCyclePullback_finite_support (f : X ⟶ Y) [IsFinite f] [Etale f]
    (c : AlgebraicCycle Y R) (hc : c.support.Finite) :
    (finiteEtaleCyclePullback f c).support.Finite :=
  f.finite_preimage hc

/-- Pullback of cycles along a finite étale surjection is injective. -/
theorem finiteEtaleCyclePullback_injective (f : X ⟶ Y) [IsFinite f] [Etale f]
    (hf : Function.Surjective f) : Injective (finiteEtaleCyclePullback (R := R) f) := by
  intro c d h
  ext y
  obtain ⟨x, rfl⟩ := hf y
  exact congrArg (fun a : AlgebraicCycle X R ↦ a x) h

/-- Descent is equality of the two pullbacks on the actual fibre product. -/
theorem existsUnique_finiteEtaleCyclePullback (f : X ⟶ Y) [IsFinite f] [Etale f]
    (hf : Function.Surjective f) (c : AlgebraicCycle X R) (hc : c.support.Finite) :
    (∃! d : AlgebraicCycle Y R, d.support.Finite ∧ finiteEtaleCyclePullback f d = c) ↔
      finiteEtaleCyclePullback (pullback.fst f f) c =
        finiteEtaleCyclePullback (pullback.snd f f) c := by
  constructor
  · rintro ⟨d, ⟨_, rfl⟩, _⟩
    ext z
    exact congrArg (fun g : (pullback f f : Scheme.{u}) ⟶ Y ↦ d (g z))
      pullback.condition
  · intro h
    have hfiber (x x' : X) (hx : f x = f x') : c x = c x' := by
      obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback x x' hx
      simpa only [finiteEtaleCyclePullback_apply, hz, hz'] using
        congrArg (fun a : AlgebraicCycle (pullback f f) R ↦ a z) h
    let s : Y → X := fun y ↦ (hf y).choose
    have hs (y : Y) : f (s y) = y := (hf y).choose_spec
    have hsupport : (support fun y ↦ c (s y)).Finite := by
      refine (hc.image f).subset fun y hy ↦ ⟨s y, hy, hs y⟩
    let d : AlgebraicCycle Y R :=
      { toFun := fun y ↦ c (s y)
        supportWithinDomain' := Set.subset_univ _
        supportLocallyFiniteWithinDomain' := fun _ _ ↦
          ⟨Set.univ, Filter.univ_mem, by simpa only [Set.univ_inter] using hsupport⟩ }
    have hd : finiteEtaleCyclePullback f d = c := by
      ext x
      exact hfiber (s (f x)) x (hs (f x))
    exact ⟨d, ⟨hsupport, hd⟩, fun d' hd' ↦
      finiteEtaleCyclePullback_injective f hf (hd'.2.trans hd.symm)⟩

end Stacks.Chow

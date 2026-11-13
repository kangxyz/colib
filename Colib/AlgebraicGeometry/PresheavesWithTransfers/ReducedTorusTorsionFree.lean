/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSplit
public import Colib.AlgebraicGeometry.Correspondences.TorsionFree

/-! # No integer torsion in the original all-axis reduced torus sections -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- Nonzero natural multiplication cancels in the original transfer torus representable. -/
theorem torusRepresentable_sections_nsmul_injective (q : ℕ) (X : Cor k)
    (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (fun x : sections (torusRepresentable k q) X => n • x) := by
  intro a b h
  apply ULift.ext
  exact Stacks.Chow.finiteCorrespondences_nsmul_injective X.toSmoothSite.hom
    (SmoothSite.torusPower (Spec (.of k)) q).hom n hn (congrArg ULift.down h)

/-- The actual common section is injective after evaluating on any correspondence object. -/
theorem reducedTorusSection_app_injective (q : ℕ) (X : Cor k) :
    Function.Injective ((reducedTorusSection k q).hom.app (op X)) := by
  let s := (reducedTorusSection k q).hom.app (op X)
  let p := (toReducedTorus k q).hom.app (op X)
  have hsp : s ≫ p = 𝟙 _ :=
    congrArg (fun f => f.hom.app (op X)) (reducedTorusSection_quotient k q)
  intro a b h
  calc
    a = p (s a) := (congrArg (fun f => f a) hsp).symm
    _ = p (s b) := congrArg p h
    _ = b := congrArg (fun f => f b) hsp

/-- The simultaneous splitting, not an arbitrary quotient argument, gives cancellation. -/
theorem reducedTorus_sections_nsmul_injective (q : ℕ) (X : Cor k)
    (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (fun x : sections (reducedTorus k q) X => n • x) := by
  intro a b h
  apply reducedTorusSection_app_injective k q X
  apply torusRepresentable_sections_nsmul_injective k q X n hn
  have hs := congrArg ((reducedTorusSection k q).hom.app (op X)) h
  simpa only [map_nsmul] using hs

end AlgebraicGeometry.PresheafWithTransfers

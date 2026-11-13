/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Normalization

/-!
# Transfers on the evaluated reduced torus comparison

On signed representatives, restriction of the lift and projection is
precomposition by the actual exterior correspondence.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "F" =>
  Cor.parameterProduct (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))

/-- The representative of a restricted section is the actual precomposition. -/
theorem torusCancellationLift_transfer_apply (Y : Cor k) {X X' : Cor k}
    (β : X' ⟶ X) (a : sections (torusCancellationTarget k Y) X) :
    ((torusCancellationLift k Y).hom.app (op X')
      (transfer (torusCancellationTarget k Y) β a)).down =
    (F).map β ≫ ((torusCancellationLift k Y).hom.app (op X) a).down := by
  let L := torusCancellationLift k Y
  let b : ULift.{u + 1} ((F).obj X ⟶ (F).obj Y) := L.hom.app (op X) a
  have h := ConcreteCategory.congr_hom (transfer_naturality L β) a
  change L.hom.app (op X') (transfer (torusCancellationTarget k Y) β a) =
    transfer ((representableLarge k).obj ((F).obj Y)) ((F).map β) b at h
  have hb : transfer ((representableLarge k).obj ((F).obj Y)) ((F).map β) b =
      ULift.up ((F).map β ≫ b.down) :=
    (congrArg (fun c : ULift.{u + 1} ((F).obj X ⟶ (F).obj Y) =>
      transfer ((representableLarge k).obj ((F).obj Y)) ((F).map β) c)
      (ULift.up_down b).symm).trans (representableLarge_transfer_apply k ((F).map β) b.down)
  exact congrArg ULift.down (h.trans hb)

/-- Projecting a signed correspondence to the reduced target commutes with
the original precomposition. -/
theorem torusCancellationProjection_transfer_apply (Y : Cor k) {X X' : Cor k}
    (β : X' ⟶ X) (a : (F).obj X ⟶ (F).obj Y) :
    transfer (torusCancellationTarget k Y) β
        ((torusCancellationProjection k Y).hom.app (op X) (ULift.up a)) =
      (torusCancellationProjection k Y).hom.app (op X') (ULift.up ((F).map β ≫ a)) := by
  let L := torusCancellationProjection k Y
  have h := ConcreteCategory.congr_hom (transfer_naturality L β) (ULift.up a)
  change L.hom.app (op X')
      (transfer ((representableLarge k).obj ((F).obj Y)) ((F).map β) (ULift.up a)) =
    transfer (torusCancellationTarget k Y) β (L.hom.app (op X) (ULift.up a)) at h
  rw [representableLarge_transfer_apply] at h
  exact h.symm

end AlgebraicGeometry.PresheafWithTransfers

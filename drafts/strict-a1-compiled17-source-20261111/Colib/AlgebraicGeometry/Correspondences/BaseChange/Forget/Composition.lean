/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.TorCycle
public import Colib.AlgebraicGeometry.Correspondences.Composition.Pairing

/-!
# Forgetting the base preserves actual signed composition

Native biadditive extensionality extends the actual prime Tor comparison to all
signed finite cycles. No composition law is supplied as a hypothesis.
Adapted from `Motivic/AlgebraicGeometry/Correspondences/BaseChange/Forget/Composition.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k L : Type u} [Field k] [Field L] {X Y Z : Scheme.{u}}
  (r : Spec (.of L) ⟶ Spec (.of k))
  (f : X ⟶ Spec (.of L)) (g : Y ⟶ Spec (.of L)) (h : Z ⟶ Spec (.of L))
  [IsSeparated r] [FormallyUnramified r] [LocallyOfFiniteType r]
  [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  [Smooth (g ≫ r)] [Smooth (h ≫ r)]

/-- Actual Tor composition commutes with the native signed pushforward map. -/
theorem finiteCorrespondencesForgetBase_incidenceTorPairing
    (a : finiteCorrespondences f g) (b : finiteCorrespondences g h) :
    finiteCorrespondencesForgetBase r f h (incidenceTorPairing f g h a b) =
      incidenceTorPairing (f ≫ r) (g ≫ r) (h ≫ r)
        (finiteCorrespondencesForgetBase r f g a)
        (finiteCorrespondencesForgetBase r g h b) := by
  let P : finiteCorrespondences f g →+ finiteCorrespondences g h →+
      finiteCorrespondences (f ≫ r) (h ≫ r) :=
    { toFun := fun a => (finiteCorrespondencesForgetBase r f h).comp
        (incidenceTorPairing f g h a)
      map_zero' := by
        ext b
        simp [incidenceTorPairing_zero_left]
      map_add' := by
        intro a a'
        ext b
        simp [incidenceTorPairing_add_left] }
  let Q : finiteCorrespondences f g →+ finiteCorrespondences g h →+
      finiteCorrespondences (f ≫ r) (h ≫ r) :=
    { toFun := fun a =>
        (incidenceTorPairing (f ≫ r) (g ≫ r) (h ≫ r)
          (finiteCorrespondencesForgetBase r f g a)).comp
          (finiteCorrespondencesForgetBase r g h)
      map_zero' := by
        ext b
        simp [incidenceTorPairing_zero_left]
      map_add' := by
        intro a a'
        ext b
        simp [incidenceTorPairing_add_left] }
  have hPQ : P = Q := by
    apply finiteCorrespondences.biaddHom_ext f g h
    intro z hz w hw
    change finiteCorrespondencesForgetBase r f h
      (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
        (singleFiniteCorrespondence g h w hw 1)) =
      incidenceTorPairing (f ≫ r) (g ≫ r) (h ≫ r)
        (finiteCorrespondencesForgetBase r f g (singleFiniteCorrespondence f g z hz 1))
        (finiteCorrespondencesForgetBase r g h (singleFiniteCorrespondence g h w hw 1))
    rw [incidenceTorPairing_single_one, finiteCorrespondencesForgetBase_single,
      finiteCorrespondencesForgetBase_single, incidenceTorPairing_single_one]
    exact finiteCorrespondencesForgetBase_incidenceTorCorrespondence r f g h z w hz hw
  exact congrArg (fun R => R a b) hPQ

end Stacks.Chow

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus
public import Colib.AlgebraicGeometry.Sites.Smooth.Torus.Reset
public import Colib.CategoryTheory.Preadditive.FiniteProjector

/-!
# The common complement of all actual identity-coordinate axes

The splitting is built on the original transfer representable by commuting
coordinate resets, and descends through the original all-axis cokernel.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- The original transfer representable map induced by resetting one coordinate. -/
def torusRepresentableReset (q : ℕ) (i : Fin q) :
    torusRepresentable k q ⟶ torusRepresentable k q :=
  (representableLarge k).map
    ((Cor.graphFunctor k).map (SmoothSite.torusReset (Spec (.of k)) q i))

/-- Each actual transfer reset is idempotent. -/
theorem torusRepresentableReset_idempotent (q : ℕ) (i : Fin q) :
    torusRepresentableReset k q i ≫ torusRepresentableReset k q i =
      torusRepresentableReset k q i := by
  unfold torusRepresentableReset
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    SmoothSite.torusReset_idempotent]

/-- The actual transfer resets commute. -/
theorem torusRepresentableReset_comm (q : ℕ) (i j : Fin q) :
    torusRepresentableReset k q i ≫ torusRepresentableReset k q j =
      torusRepresentableReset k q j ≫ torusRepresentableReset k q i := by
  unfold torusRepresentableReset
  simp only [← CategoryTheory.Functor.map_comp, SmoothSite.torusReset_comm _ _ i j]

/-- The corresponding identity axis is fixed by its reset. -/
@[reassoc]
theorem torusIdentityAxis_reset (q : ℕ) (i : Fin q) :
    torusIdentityAxis k q i ≫ torusRepresentableReset k q i =
      torusIdentityAxis k q i := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    change (representableLarge k).map ((Cor.graphFunctor k).map
        (SmoothSite.torusInsertOne (Spec (.of k)) q i)) ≫
      (representableLarge k).map ((Cor.graphFunctor k).map
        (SmoothSite.torusReset (Spec (.of k)) (q + 1) i)) =
      (representableLarge k).map ((Cor.graphFunctor k).map
        (SmoothSite.torusInsertOne (Spec (.of k)) q i))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      SmoothSite.torusReset_eq_delete_insert, ← Category.assoc,
      SmoothSite.torusInsertOne_deleteCoordinate, Category.id_comp]

/-- Every reset factors through an axis killed by the original reduced quotient. -/
@[reassoc (attr := simp)]
theorem torusRepresentableReset_toReducedTorus (q : ℕ) (i : Fin q) :
    torusRepresentableReset k q i ≫ toReducedTorus k q = 0 := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    unfold torusRepresentableReset
    rw [SmoothSite.torusReset_eq_delete_insert,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc]
    change _ ≫ (torusIdentityAxis k (q + 1) i ≫ toReducedTorus k (q + 1)) = 0
    rw [torusIdentityAxis_toReducedTorus, comp_zero]

/-- The ordered product of all complementary resets on the original representable. -/
def torusJointProjector (q : ℕ) : torusRepresentable k q ⟶ torusRepresentable k q :=
  complementaryProjector (torusRepresentableReset k q) (List.ofFn (fun i : Fin q => i))

/-- Every identity axis is killed by the common projector, not merely one chosen axis. -/
@[reassoc]
theorem torusIdentityAxis_jointProjector (q : ℕ) (i : Fin q) :
    torusIdentityAxis k q i ≫ torusJointProjector k q = 0 := by
  calc
    _ = (torusIdentityAxis k q i ≫ torusRepresentableReset k q i) ≫
        torusJointProjector k q := by rw [torusIdentityAxis_reset]
    _ = 0 := by
      rw [Category.assoc]
      have h := comp_complementaryProjector_eq_zero (torusRepresentableReset k q)
        (torusRepresentableReset_idempotent k q) (torusRepresentableReset_comm k q)
        (List.ofFn (fun j : Fin q => j)) i (by simp)
      change torusIdentityAxis k q i ≫
        (torusRepresentableReset k q i ≫
          complementaryProjector (torusRepresentableReset k q) _) = 0
      rw [h, comp_zero]

/-- The common projector retains the original reduced quotient. -/
@[reassoc (attr := simp)]
theorem torusJointProjector_toReducedTorus (q : ℕ) :
    torusJointProjector k q ≫ toReducedTorus k q = toReducedTorus k q :=
  complementaryProjector_comp (torusRepresentableReset k q) (toReducedTorus k q)
    (torusRepresentableReset_toReducedTorus k q) _

/-- A simultaneous section of the original all-axis quotient, natural for signed transfers. -/
def reducedTorusSection (q : ℕ) : reducedTorus k q ⟶ torusRepresentable k q :=
  reducedTorusDesc k q (torusJointProjector k q) (torusIdentityAxis_jointProjector k q)

/-- The actual quotient followed by its section is the common projector. -/
@[reassoc]
theorem toReducedTorus_section (q : ℕ) :
    toReducedTorus k q ≫ reducedTorusSection k q = torusJointProjector k q :=
  toReducedTorus_desc k q _ _

/-- The section followed by the original quotient is the identity. -/
@[reassoc (attr := simp)]
theorem reducedTorusSection_quotient (q : ℕ) :
    reducedTorusSection k q ≫ toReducedTorus k q = 𝟙 (reducedTorus k q) := by
  apply reducedTorus_hom_ext
  rw [← Category.assoc, toReducedTorus_section, torusJointProjector_toReducedTorus,
    Category.comp_id]

end AlgebraicGeometry.PresheafWithTransfers

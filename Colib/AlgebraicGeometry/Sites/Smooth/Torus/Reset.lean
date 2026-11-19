/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Torus

/-! # Commuting resets of the coordinates of the actual relative torus -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Maps between torus powers retain their common structure map. -/
@[reassoc (attr := simp)]
theorem torusPowerToBase_naturality (S : Scheme.{u}) {p q : ℕ}
    (f : torusPower S p ⟶ torusPower S q) :
    f ≫ torusPowerToBase S q = torusPowerToBase S p := by
  apply MorphismProperty.Over.Hom.ext
  exact MorphismProperty.Over.w f

/-- Set one coordinate to the actual identity section, retaining all others. -/
def torusReset (S : Scheme.{u}) (q : ℕ) (i : Fin q) :
    torusPower S q ⟶ torusPower S q :=
  torusPowerLift S q (fun j =>
    if j = i then torusPowerToBase S q ≫ torusOne S else torusCoordinate S q j)

/-- The coordinate formula for a reset is literal, not only up to isomorphism. -/
@[reassoc (attr := simp)]
theorem torusReset_coordinate (S : Scheme.{u}) (q : ℕ) (i j : Fin q) :
    torusReset S q i ≫ torusCoordinate S q j =
      if j = i then torusPowerToBase S q ≫ torusOne S else torusCoordinate S q j := by
  simp [torusReset]

/-- Resetting twice is the same as resetting once. -/
@[reassoc (attr := simp)]
theorem torusReset_idempotent (S : Scheme.{u}) (q : ℕ) (i : Fin q) :
    torusReset S q i ≫ torusReset S q i = torusReset S q i := by
  apply torusPower_hom_ext
  intro j
  by_cases h : j = i <;> simp [Category.assoc, h]

/-- Different coordinate resets commute on the original torus power. -/
theorem torusReset_comm (S : Scheme.{u}) (q : ℕ) (i j : Fin q) :
    torusReset S q i ≫ torusReset S q j = torusReset S q j ≫ torusReset S q i := by
  apply torusPower_hom_ext
  intro a
  by_cases hi : a = i <;> by_cases hj : a = j <;> simp_all [Category.assoc]

/-- The reset factors through the genuine identity-coordinate axis. -/
theorem torusReset_eq_delete_insert (S : Scheme.{u}) (q : ℕ) (i : Fin (q + 1)) :
    torusReset S (q + 1) i =
      torusDeleteCoordinate S q i ≫ torusInsertOne S q i := by
  apply torusPower_hom_ext
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨a, rfl⟩
  · simp [Category.assoc]
  · simp [Category.assoc, Fin.succAbove_ne]

end AlgebraicGeometry.Scheme.SmoothSite

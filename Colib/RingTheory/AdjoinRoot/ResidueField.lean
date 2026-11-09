/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.RingTheory.AdjoinRoot.LocalRing

/-!
# The actual residue field of a polynomial root algebra

When the reduction of a polynomial over a local ring is irreducible, the residue
field of its actual local AdjoinRoot algebra is the AdjoinRoot of its literal
residue polynomial. This comparison preserves the images of every polynomial,
not just the chosen root. Its construction composes the existing quotient equality
with Mathlib's quotEquivQuotMap, with no replacement residue field or local ring.

The local structure is the existing native one; for a monic polynomial it is
supplied by AdjoinRoot.isLocalRing_of_irreducible_map_residue.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace AdjoinRoot

variable {A : Type*} [CommRing A] [IsLocalRing A] (p : A[X])
  [IsLocalRing (AdjoinRoot p)]

/-- Identify the original local root algebra's actual residue field with the
literal residue-polynomial root algebra. -/
def residueFieldEquivAdjoinRoot (hirr : Irreducible (p.map (residue A))) :
    ResidueField (AdjoinRoot p) ≃+* AdjoinRoot (p.map (residue A)) :=
  (Ideal.quotEquivOfEq (maximalIdeal_eq_map_maximalIdeal hirr)).trans
    (quotEquivQuotMap p (maximalIdeal A)).toRingEquiv

/-- The residue comparison preserves the class of every original polynomial. -/
theorem residueFieldEquivAdjoinRoot_residue_mk
    (hirr : Irreducible (p.map (residue A))) (q : A[X]) :
    residueFieldEquivAdjoinRoot p hirr (residue (AdjoinRoot p) (mk p q)) =
      mk (p.map (residue A)) (q.map (residue A)) := by
  change quotEquivQuotMap p (maximalIdeal A)
    (Ideal.Quotient.mk ((maximalIdeal A).map (of p)) (mk p q)) = _
  exact quotEquivQuotMap_apply_mk p q (maximalIdeal A)

/-- The actual residue of the original root is the root of the literal reduction. -/
@[simp]
theorem residueFieldEquivAdjoinRoot_residue_root
    (hirr : Irreducible (p.map (residue A))) :
    residueFieldEquivAdjoinRoot p hirr (residue (AdjoinRoot p) (root p)) =
      root (p.map (residue A)) := by
  simpa only [map_X, mk_X] using residueFieldEquivAdjoinRoot_residue_mk p hirr X

/-- The comparison preserves every original base-ring coefficient under residue. -/
theorem residueFieldEquivAdjoinRoot_residue_of
    (hirr : Irreducible (p.map (residue A))) (a : A) :
    residueFieldEquivAdjoinRoot p hirr (residue (AdjoinRoot p) (of p a)) =
      of (p.map (residue A)) (residue A a) := by
  simpa only [map_C, mk_C] using residueFieldEquivAdjoinRoot_residue_mk p hirr (C a)

end AdjoinRoot

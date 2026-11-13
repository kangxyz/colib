/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian

/-! # The object property of A¹-invariant transfer presheaves -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The actual affine projection remains invertible under a coefficient isomorphism. -/
theorem IsA1Invariant.of_iso {P Q : PresheafWithTransfers.{v} k}
    (hP : P.IsA1Invariant) (e : P ≅ Q) : Q.IsA1Invariant := by
  intro X
  exact (NatIso.isIso_map_iff ((toPresheaf k).mapIso e)
    ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op).1 (hP X)

/-- A zero coefficient is invariant under the original affine projection. -/
theorem isA1Invariant_of_isZero {P : PresheafWithTransfers.{v} k} (hP : IsZero P) :
    P.IsA1Invariant := by
  intro X
  let U (Y : SmoothSite (Spec (.of k))) :=
    toPresheaf.{v} k ⋙ (CategoryTheory.evaluation _ AddCommGrpCat.{v}).obj (op Y)
  exact ((U X).map_isZero hP).isIso ((U (affineLineCylinder.obj X)).map_isZero hP) _

/-- The canonical object property defined by coefficient A¹-invariance. -/
abbrev a1InvariantProperty (k : Type u) [Field k] :
    ObjectProperty (PresheafWithTransfers.{v} k) :=
  fun P => P.IsA1Invariant

instance (k : Type u) [Field k] : (a1InvariantProperty.{v} k).IsClosedUnderIsomorphisms where
  of_iso e hP := hP.of_iso e

instance (k : Type u) [Field k] : (a1InvariantProperty.{v} k).ContainsZero where
  exists_zero := by
    obtain ⟨P, hP⟩ := HasZeroObject.zero (C := PresheafWithTransfers.{v} k)
    exact ⟨P, hP, isA1Invariant_of_isZero hP⟩

end AlgebraicGeometry.PresheafWithTransfers

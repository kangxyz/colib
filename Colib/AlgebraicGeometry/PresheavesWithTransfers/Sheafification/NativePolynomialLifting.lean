/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.NativePolynomialGeometry
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.PairedMiddleLift

/-! # Lifting the original representatives using the actual paired actions -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

/-- The actual paired actions lift the matching original polynomial representatives. -/
theorem nisnevichImage_lift_of_nativePolynomialRepresentatives
    {k : Type u} [Field k] (R : Type u) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [IsNoetherianRing R] [Algebra k R] [Algebra.FiniteType k R]
    (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
    (Pst : PresheafWithTransfers.{u + 1} k) (hPst : Pst.IsA1Invariant) :
    NativePolynomialRepresentativeLifting R t Pst :=
  nativePolynomialRepresentativeLifting_of_pairedSectionCylinderLifting R t
    (@nisnevichImage_wholeCylinder_lift_of_pairedSectionData k _) Pst hPst

end AlgebraicGeometry.PresheafWithTransfers

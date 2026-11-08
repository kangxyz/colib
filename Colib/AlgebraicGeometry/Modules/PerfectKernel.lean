/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectWaldhausen

/-! # Native perfect kernels and shifts

The native Stacks first-vertex theorem for a distinguished triangle gives
perfectness of the actual kernel in a short exact sequence. Native derived
shift closure similarly applies to the original shifted complex.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry StrictlyPerfect
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.RingedSpace
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
variable (X : RingedSpace.{u, u})

/-- The actual kernel term is perfect when the other terms of a short exact sequence are. -/
@[stacks 08CR "First-vertex specialization to an actual short exact sequence"]
theorem isPerfectComplex_X₁_of_shortExact
    {S : ShortComplex (CochainComplex (OXMod.{u, u, u} X) ℤ)} (hS : S.ShortExact)
    (h₂ : IsPerfectComplex S.X₂) (h₃ : IsPerfectComplex S.X₃) :
    IsPerfectComplex S.X₁ := by
  let : HasDerivedCategory.{u + 1} (OXMod.{u, u, u} X) := HasDerivedCategory.standard _
  have h : IsPerfect (DerivedCategory.Q.obj S.X₁) :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished
      (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS)
      h₂.isPerfect h₃.isPerfect
  exact isPerfectComplex_of_isPerfect_representation h ⟨Iso.refl _⟩

/-- Shifts retain native perfectness of the actual complex. -/
theorem isPerfectComplex_shift {K : CochainComplex (OXMod.{u, u, u} X) ℤ}
    (hK : IsPerfectComplex K) (n : ℤ) : IsPerfectComplex (K⟦n⟧) := by
  let : HasDerivedCategory.{u + 1} (OXMod.{u, u, u} X) := HasDerivedCategory.standard _
  exact isPerfectComplex_of_isPerfect_representation
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hK.isPerfect n)
    ⟨(DerivedCategory.Q.commShiftIso n).app K⟩

end AlgebraicGeometry.RingedSpace

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FieldCoefficientFrames

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil

#check nonempty_frame_of_finite_over_field
#check nonempty_lambdaCoefficientBoundaryFrame
#check nonempty_psiCoefficientBoundaryFrame

example {k : Type*} [Field k] {Z : Scheme} (b : Z ⟶ Spec (.of k)) [IsFinite b]
    (M : Z.Modules) [IsInvertibleModule Z M] : Nonempty (M ≅ SheafOfModules.unit Z.ringCatSheaf) :=
  nonempty_frame_of_finite_over_field b M

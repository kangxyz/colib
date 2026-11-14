/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.PerfectPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentativeUnconditional
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf

/-! # Strict perfect representatives on the projective line

Over an arbitrary affine base, the native ample twisting sheaf supplies
the resolution property and a bounded finite locally free representative.
The comparison takes place in the original bounded-below derived category.

* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
-/

public noncomputable section

open CategoryTheory
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard

/-- An intrinsic perfect object in the bounded-below derived category of the
projective line has a global bounded finite locally free representative. -/
theorem exists_projectiveLinePerfectRepresentative (R : CommRingCat.{u})
    (K : DerivedCategory.Plus (projectiveSpaceOver 1 (Spec R)).Modules)
    (hK : RingedSpace.IsPerfect (X := (projectiveSpaceOver 1 (Spec R)).toRingedSpace)
      (DerivedCategory.Plus.ι.obj K)) :
    ∃ E : CochainComplex (projectiveSpaceOver 1 (Spec R)).Modules ℤ,
      ∃ hE : boundedFiniteLocallyFreeComplex (projectiveSpaceOver 1 (Spec R)) E,
        Nonempty (DerivedCategory.Plus.Q.obj ⟨E, hE.1.1⟩ ≅ K) := by
  let X := projectiveSpaceOver 1 (Spec R)
  let L := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 1 (Spec R)
  obtain ⟨E, hE, ⟨e⟩⟩ :=
    exists_boundedFiniteLocallyFree_iso_of_isAmple X L
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf 1 (Spec R)) K.obj hK
  exact ⟨E, hE, ⟨DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.Plus.QCompιIso X.Modules).app ⟨E, hE.1.1⟩ ≪≫ e)⟩⟩

end AlgebraicGeometry.projectiveSpaceOver

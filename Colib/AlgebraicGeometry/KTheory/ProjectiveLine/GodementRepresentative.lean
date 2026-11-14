/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BoundedBelowComparison
public import StacksFrontier.AlgebraicGeometry.Cohomology.GodementBoundedBelowResolution

/-! # Godement representatives of bounded below perfect complexes

The native Godement total complex has the same lower term bound, has flasque terms, and is
perfect by its augmentation quasi-isomorphism. No replacement of the perfectness predicate
is made.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.GodementResolution
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect

universe u

variable {X : Scheme.{u}}

/-- The native Godement double complex of a bounded below perfect complex admits totalization. -/
instance godementHasTotal (K : Obj X) :
    (godementDoubleComplex X.toRingedSpace K.obj).HasTotal (ComplexShape.up ℤ) := by
  obtain ⟨a, ha⟩ := K.property.2
  let h : (show CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ
      from K.obj).IsStrictlyGE a := ha
  exact HomologicalComplex₂.hasTotal_of_finite _ _
    (finite_diagonal_godementDoubleComplex X.toRingedSpace K.obj a)

/-- The actual Godement representative preserves native perfectness and the lower term bound. -/
theorem godementTotal_mem (K : Obj X) :
    objects X ((godementDoubleComplex X.toRingedSpace K.obj).total (ComplexShape.up ℤ)) := by
  obtain ⟨a, ha⟩ := K.property.2
  let h : (show CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ
      from K.obj).IsStrictlyGE a := ha
  obtain ⟨hq, hge, _⟩ :=
    exists_quasiIso_isStrictlyGE_isFlasque_godement X.toRingedSpace K.obj a
  exact ⟨K.property.1.of_quasiIso (godementComparisonMap X.toRingedSpace K.obj a) hq, a, hge⟩

/-- Every term of the actual Godement representative is flasque. -/
theorem godementTotal_isFlasque (K : Obj X) (i : ℤ) :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj
        (((godementDoubleComplex X.toRingedSpace K.obj).total (ComplexShape.up ℤ)).X i)) := by
  obtain ⟨a, ha⟩ := K.property.2
  let h : (show CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ
      from K.obj).IsStrictlyGE a := ha
  exact (exists_quasiIso_isStrictlyGE_isFlasque_godement X.toRingedSpace K.obj a).2.2 i

end AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect

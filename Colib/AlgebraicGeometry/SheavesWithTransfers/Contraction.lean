/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Continuity
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionInvariance
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Limits

/-!
# Actual contraction of HI Nisnevich sheaves with transfers

Continuity proves sheafness of parameter sections. The actual unit kernel is
then a sheaf by closure under limits. Coefficient HI identifies the given
Laurent cokernel with that kernel, without asserting sheafness for arbitrary
cokernels or replacing the quotient by its sheafification.
Adapted from `Motivic/Transfers/Presheaf/ContractionSheaf.lean:52-105`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Actual parameter products preserve Nisnevich sheafness without a HI premise. -/
theorem withParameter_isNisnevichSheaf (P : PresheafWithTransfers.{v} k)
    (hP : IsNisnevichSheaf k P) (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] : IsNisnevichSheaf k (withParameter P T) := by
  apply (Presheaf.isSheaf_of_iso_iff (withParameterUnderlyingIso P T)).mpr
  exact (SmoothSite.Contraction.parameterProduct T).op_comp_isSheaf_of_isSheaf _ _ _ hP

/-- Graph restriction takes the genuine transfer kernel to the same ordinary kernel. -/
def contractionKernelUnderlyingIso (P : PresheafWithTransfers.{v} k) :
    (toPresheaf k).obj (contractionKernel P) ≅
      kernel ((toPresheaf k).map (torusUnit P)) :=
  PreservesKernel.iso (toPresheaf k) (torusUnit P)

/-- The unit kernel is a genuine sheaf, using parameter continuity and only limits. -/
theorem contractionKernel_isNisnevichSheaf (P : PresheafWithTransfers.{v} k)
    (hP : IsNisnevichSheaf k P) : IsNisnevichSheaf k (contractionKernel P) := by
  apply (Presheaf.isSheaf_of_iso_iff (contractionKernelUnderlyingIso P)).mpr
  apply ObjectProperty.prop_limit
    (Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) (A := AddCommGrpCat.{v}))
    (parallelPair ((toPresheaf k).map (torusUnit P)) 0)
  intro j
  cases j with
  | zero =>
    exact withParameter_isNisnevichSheaf P hP
      (SmoothSite.multiplicativeGroupObject (Spec (.of k)))
  | one =>
    exact withParameter_isNisnevichSheaf P hP (SmoothSite.base (Spec (.of k)))

/-- For already HI sheaves the literal presheaf cokernel, not its sheafification, is a sheaf. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/ContractionSheaf.lean:79-85"
  "adaptation" "Actual coefficient HI, native Nisnevich continuity and genuine unit kernel"]
theorem contraction_isNisnevichSheaf (P : PresheafWithTransfers.{v} k)
    (hP : IsNisnevichSheaf k P) (hHI : IsA1Invariant P) :
    IsNisnevichSheaf k (contraction P) :=
  (Presheaf.isSheaf_of_iso_iff
    ((toPresheaf k).mapIso (contractionIsoKernel P hHI))).mpr
      (contractionKernel_isNisnevichSheaf P hP)

end AlgebraicGeometry.PresheafWithTransfers

namespace AlgebraicGeometry.SheafWithTransfers

variable {k : Type u} [Field k]

/-- Contraction of an HI sheaf, with exactly the already defined signed-transfer quotient. -/
def contraction (F : SheafWithTransfers.{v} k) (hF : F.obj.IsA1Invariant) :
    SheafWithTransfers.{v} k :=
  ⟨PresheafWithTransfers.contraction F.obj,
    PresheafWithTransfers.contraction_isNisnevichSheaf F.obj F.property hF⟩

@[simp]
theorem contraction_obj (F : SheafWithTransfers.{v} k) (hF : F.obj.IsA1Invariant) :
    (contraction F hF).obj = PresheafWithTransfers.contraction F.obj := rfl

/-- This same sheaf is again coefficient homotopy invariant. -/
theorem contraction_isA1Invariant (F : SheafWithTransfers.{v} k)
    (hF : F.obj.IsA1Invariant) : (contraction F hF).obj.IsA1Invariant :=
  PresheafWithTransfers.contraction_isA1Invariant F.obj hF

end AlgebraicGeometry.SheafWithTransfers

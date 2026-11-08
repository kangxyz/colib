/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCanonicalNullTrack


/-! The same canonical null, global zero-normalization and full rotated boundary. -/
public section
open Topology SSet
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Topology AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
    CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum
open scoped Topology
universe u
namespace ColibTest.ScalarTrack.ScalarCofiberCanonicalNull
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
local notation "hA" => perfectOpenScalarConeFunctor_waldhausenExact j r q hq
local notation "Ar" => CategoryTheory.rebaseFunctor (perfectOpenScalarConeFunctor j r q hq)
  (Structure.zero V) (Structure.zero (acyclicStructure N))
  (Limits.IsZero.iso (IsExact.zero hA (Structure.isZero V))
    (Structure.isZero (acyclicStructure N)))

/-- The actual canonical fiber path has the same reversed zero-to-inclusion cylinder. -/
theorem original_fiber_path (t : unitInterval) (x : (V).Delooping) :
    (canonicalFiberMap N (deloopingMap (hA).rebase x)).val.2 t =
      weakNaturalTransformationRealizationHomotopy V W
        ((hA).rebase.comp (zeroFunctor_isExact (acyclicStructure N) W))
        ((hA).rebase.comp (acyclicInclusion_coarse_exact N))
        (perfectOpenScalarRebasedZeroToCone j r q hq)
        (fun K => zeroToAcyclicInclusion_weak N ((Ar).obj K)) (unitInterval.symm t, x) :=
  perfectOpenScalarCanonicalNull_rebased_apply j r q hq t x

/-- Every input, not only the zero input, has the unchanged constant normalization track. -/
theorem original_global_zero_track (t : unitInterval) (x : (V).Delooping) :
    weakNaturalTransformationRealizationHomotopy V W
        (perfectOpenScalarIdentityCofibrationSequence j).exactH.rebase (zeroFunctor_isExact V W)
        (perfectOpenScalarZeroRebaseIso j).inv
        (fun K => (W).weq_iso _
          (show IsIso ((perfectOpenScalarZeroRebaseIso j).app K).inv from inferInstance)) (t, x) =
      (W).kBasepoint :=
  perfectOpenScalarZeroNormalizationRealization_constant j t x

/-- The actual cone comparison still contains both named normalization factors. -/
theorem original_cone_normalization :
    perfectOpenScalarConeNormalizationIso j r q hq =
      (perfectOpenScalarConeRebaseIso j r).symm ≪≫
        Functor.isoWhiskerRight (perfectOpenScalarAcyclicConeRebaseIso j r q hq)
          (acyclicInclusion N) := rfl

/-- Rotation keeps the independent original structure time at every level. -/
theorem original_null_triangle_structure (n : ℕ) (a s t : unitInterval)
    (x : (originalPrespectrum V).space n) :
    (perfectOpenScalarCanonicalNullTriangle j r q hq).level (n + 1)
        (a, (s, (originalPrespectrum V).structureMap n x t)) =
      (originalPrespectrum W).structureMap n
        ((perfectOpenScalarCanonicalNullTriangle j r q hq).level n (a, (s, x))) t :=
  (perfectOpenScalarCanonicalNullTriangle j r q hq).comm n a s x t

end ColibTest.ScalarTrack.ScalarCofiberCanonicalNull

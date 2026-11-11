/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.Pairing
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycleImages
public import Colib.AlgebraicGeometry.Correspondences.Exterior.FlatPullbackIdentification
public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceTorCycle
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Native exterior compatibility of actual incidence Tor composition

Let `X`, `Y`, `Z`, and `T` be smooth-site objects over a field, with `T`
geometrically integral. The existing `nativeExterior` commutes with the existing
`incidenceTorPairing`, first on actual admissible prime pairs and then on all
signed native finite correspondences.

For an original generic incidence point `η`, let `dη` be its own relative
dimension and let `aη` be its actual alternating Tor coefficient. The actual
finite outer pushforward of `aη[η]` is the admissible image singleton weighted by
`aη * residueDegree η`. Its membership in grade `dη` follows from the existing
proper-pushforward subtype. This supplies the particular graded input required
by `nativeExterior_eq_diagonal_flatPullback`; no common grade for the incidence
or its Tor cycle is imposed.

Native finite push-pull then identifies this image's exterior cycle with the
outer pushforward of `e_* p^*(aη[η])`. Sum over all original generic labels using
`incidenceTorCorrespondence_eq_sum_single` and the actual exterior Tor-cycle
transport. Repeated image points and signed cancellation remain inside the
existing additive subgroup. Biadditive extensionality extends the prime-pair
comparison without introducing another pairing or correspondence model.

The proof uses Colib e7697ab8164435c7093665d02ac34f021eefb75e,
`Composition/TorCycleImages.lean:96-114`, `Composition/Pairing.lean:67-72`, and
`Additive/Ext.lean:95-105`, relative to `Colib/AlgebraicGeometry/Correspondences`.
The actual cycle transport, finite push-pull, and target identification are the
three named imported interfaces, with their existing geometric hypotheses.
The finite push-pull input is Stacks 02RG, as implemented at
Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7 in
`StacksFrontier/AlgebraicGeometry/Chow/FlatPullback`, at
`ProperPushforwardBaseChangeUnconditional.lean:163-192`.
That input alone is not the full composition comparison proved here.
The signed extension uses the generated additive `compl₂` and `compr₂` from
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
`Mathlib/Algebra/Group/Hom/Instances.lean:278-299`.

All finite residue degrees are retained. Degree one is used only by the imported
isomorphism and common-parameter closed-immersion formulas. In particular, a
local fiber of module length one is not identified with a residue extension of
degree one. No perfection, separability, reduced-incidence, support-flatness,
coefficient-regularity, or global equidimensionality assumption is introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin
open scoped BigOperators

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]

section PrimePairs

variable (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

local notation3 (prettyPrint := false) "C" => fieldChowSituation k
local notation3 (prettyPrint := false) "fX" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "fY" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "fZ" => (SmoothSite.product Z T).hom
local notation3 (prettyPrint := false) "z'" => nativeExteriorPoint X Y T z hz
local notation3 (prettyPrint := false) "w'" => nativeExteriorPoint Y Z T w hw
local notation3 (prettyPrint := false) "hz'" => nativeExteriorPoint_admissible X Y T z hz
local notation3 (prettyPrint := false) "hw'" => nativeExteriorPoint_admissible Y Z T w hw
local notation3 (prettyPrint := false) "I" =>
  correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "q" =>
  correspondenceIncidenceMap X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "q'" =>
  correspondenceIncidenceMap fX fY fZ z' w'
local notation3 (prettyPrint := false) "sI" =>
  (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom)
local notation3 (prettyPrint := false) "sB" => (pullback.fst X.hom Z.hom ≫ X.hom)
local notation3 (prettyPrint := false) "πI" =>
  exteriorIncidenceProductProjection X Y Z T z w
local notation3 (prettyPrint := false) "sIT" => (πI ≫ sI)
local notation3 (prettyPrint := false) "e" => nativeExteriorIncidenceIso X Y Z T z w hz hw
local notation3 (prettyPrint := false) "r" => exteriorParameterDimension T

local instance : LocallyOfFiniteType sI := by
  dsimp only [correspondenceIncidenceLeft]
  infer_instance

local instance : IsLocallyNoetherian I :=
  LocallyOfFiniteType.isLocallyNoetherian (show I ⟶ Spec (.of k) from sI)

/-- Exterior of an actual signed generic image is the outer pushforward of its
actual parameter pullback. The image retains its own finite residue degree. -/
@[stacks 02RG "pointwise finite push-pull, followed by identification with the existing exterior"]
theorem nativeExterior_incidenceImage_single (η : genericPoints I) (n : ℤ) :
    let := isFinite_correspondenceIncidenceMap fX fY fZ z' w' hz' hw'
    (nativeExterior X Z T
      (singleFiniteCorrespondence X.hom Z.hom ((q).base η.val)
        (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic
          X.hom Y.hom Z.hom z w hz hw η)
        (n * ((q).residueDegree η.val : ℤ)))).val =
      finiteCyclePushforward q'
        (finiteCyclePushforward (e).hom
          (flatPullback C sIT sI πI rfl r
            (relativeDimension_exteriorIncidenceProductProjection X Y Z T z w)
            (relativeDimension (C).dimensionFunction sI η.val)
            (pointCycleAtOwnDimension C sI η.val n)).val) := by
  let := isFinite_correspondenceIncidenceMap X.hom Y.hom Z.hom z w hz hw
  let := isFinite_correspondenceIncidenceMap fX fY fZ z' w' hz' hw'
  let d := relativeDimension (C).dimensionFunction sI η.val
  let β : CycleGroup C sI d := pointCycleAtOwnDimension C sI η.val n
  let γ : finiteCorrespondences X.hom Z.hom :=
    singleFiniteCorrespondence X.hom Z.hom ((q).base η.val)
      (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic
        X.hom Y.hom Z.hom z w hz hw η)
      (n * ((q).residueDegree η.val : ℤ))
  have hq : q ≫ sB = sI := by
    simp only [← Category.assoc, correspondenceIncidenceMap_fst]
  have hval : (properPushforward C sI sB q hq d β).val = γ.val := by
    rw [properPushforward_val_eq_finiteCyclePushforward]
    change finiteCyclePushforward q (single η.val n) =
      single ((q).base η.val) (n * ((q).residueDegree η.val : ℤ))
    exact finiteCyclePushforward_single q η.val n
  have hγ : γ.val ∈ cyclesOfDimension C sB d := by
    rw [← hval]
    exact (properPushforward C sI sB q hq d β).property
  have hγpush : (⟨γ.val, hγ⟩ : CycleGroup C sB d) =
      properPushforward C sI sB q hq d β := Subtype.ext hval.symm
  change (nativeExterior X Z T γ).val = _
  rw [nativeExterior_eq_diagonal_flatPullback X Z T d γ hγ, hγpush]
  exact (nativeExteriorIncidence_pushforward_flatPullback X Y Z T z w hz hw d β).symm

/-- Actual prime-pair incidence Tor composition commutes with the existing native
exterior operation, retaining every original generic label and residue degree. -/
theorem nativeExterior_incidenceTorCorrespondence :
    nativeExterior X Z T
      (incidenceTorCorrespondence X.hom Y.hom Z.hom z w hz hw) =
      incidenceTorCorrespondence fX fY fZ z' w' hz' hw' := by
  classical
  let := (finite_genericPoints_correspondenceIncidence_of_smooth
    X.hom Y.hom Z.hom z w hw).fintype
  let := isFinite_correspondenceIncidenceMap fX fY fZ z' w' hz' hw'
  let γ : genericPoints I → finiteCorrespondences X.hom Z.hom := fun η =>
    singleFiniteCorrespondence X.hom Z.hom ((q).base η.val)
      (isFiniteCorrespondencePoint_correspondenceIncidenceMap_generic
        X.hom Y.hom Z.hom z w hz hw η)
      (correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w η *
        ((q).residueDegree η.val : ℤ))
  have hsum : incidenceTorCorrespondence X.hom Y.hom Z.hom z w hz hw = ∑ η, γ η :=
    incidenceTorCorrespondence_eq_sum_single X.hom Y.hom Z.hom z w hz hw
  apply Subtype.ext
  calc
    (nativeExterior X Z T
        (incidenceTorCorrespondence X.hom Y.hom Z.hom z w hz hw)).val =
        ∑ η : genericPoints I, (nativeExterior X Z T (γ η)).val := by
      change (finiteCorrespondences fX fZ).subtype
        (nativeExterior X Z T (incidenceTorCorrespondence X.hom Y.hom Z.hom z w hz hw)) = _
      rw [hsum, map_sum, map_sum]
      rfl
    _ = ∑ η : genericPoints I,
        finiteCyclePushforward q'
          (finiteCyclePushforward (e).hom
            (flatPullback C sIT sI πI rfl r
              (relativeDimension_exteriorIncidenceProductProjection X Y Z T z w)
              (relativeDimension (C).dimensionFunction sI η.val)
              (pointCycleAtOwnDimension C sI η.val
                (correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w η))).val) := by
      apply Finset.sum_congr rfl
      intro η hη
      exact nativeExterior_incidenceImage_single X Y Z T z w hz hw η _
    _ = finiteCyclePushforward q' (incidenceTorCycle fX fY fZ z' w' hw') := by
      rw [incidenceTorCycle_nativeExterior_eq_sum_incidenceIso_flatPullback, map_sum]
    _ = (incidenceTorCorrespondence fX fY fZ z' w' hz' hw').val :=
      (incidenceTorCorrespondence_val fX fY fZ z' w' hz' hw').symm

end PrimePairs

/-- Equality of the two actual biadditive maps. Coefficient-one prime pairs
suffice because the native finite-correspondence subgroups are generated by them. -/
theorem nativeExterior_incidenceTorPairing_hom :
    (incidenceTorPairing X.hom Y.hom Z.hom).compr₂ (nativeExterior X Z T) =
      ((incidenceTorPairing (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom).compl₂
          (nativeExterior Y Z T)).comp (nativeExterior X Y T) := by
  apply finiteCorrespondences.biaddHom_ext X.hom Y.hom Z.hom
  intro z hz w hw
  simp only [AddMonoidHom.compr₂_apply, AddMonoidHom.comp_apply,
    AddMonoidHom.compl₂_apply, nativeExterior_single, one_zsmul,
    nativeExteriorPrime_eq_single, incidenceTorPairing_single_one]
  exact nativeExterior_incidenceTorCorrespondence X Y Z T z w hz hw

/-- Exterior product with the geometrically integral parameter identity preserves
actual incidence Tor composition for arbitrary signed native correspondences. -/
theorem nativeExterior_incidenceTorPairing
    (α : finiteCorrespondences X.hom Y.hom) (β : finiteCorrespondences Y.hom Z.hom) :
    nativeExterior X Z T (incidenceTorPairing X.hom Y.hom Z.hom α β) =
      incidenceTorPairing (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
        (SmoothSite.product Z T).hom (nativeExterior X Y T α) (nativeExterior Y Z T β) := by
  exact congrArg
    (fun F : finiteCorrespondences X.hom Y.hom →+ finiteCorrespondences Y.hom Z.hom →+
      finiteCorrespondences (SmoothSite.product X T).hom (SmoothSite.product Z T).hom => F α β)
    (nativeExterior_incidenceTorPairing_hom X Y Z T)

end Stacks.Chow

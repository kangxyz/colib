/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteImageLabels
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFirstCoefficientEuler
public import Colib.RingTheory.Koszul.GenericFiniteReindex

/-!
# Actual original exterior labels regrouped by their literal image-stalk primes

The finite-model structure map defines the image-prime map on every retained
original exterior generic label. Nonminimal images are not omitted by a
geometric dominance assumption: the actual generic remaining intersection gives
an ideal of definition, and native generic Euler devissage makes precisely those
quotient Euler factors zero. The remaining finite regrouping uses the proved
fibre-label equivalence, preserving each original first Tor coefficient, full
closed-fibre length, and finite-map residue degree.

This is the geometric reindexing needed to connect the concrete whole finite
Tor family to the fixed-original-label remaining Euler formula. It imports no
coherent Tor sheaf construction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))

local notation3 (prettyPrint := false) "E" =>
  correspondenceLeftIntermediateSupportProduct f g h i z w v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "R" =>
  correspondenceRemainingImageStalk f g h i z w v x.1
local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x.1
local notation3 (prettyPrint := false) "q'" =>
  correspondenceLeftIntermediateImageMap f g h i z w v
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "L" =>
  correspondenceRemainingOriginalGenericLabels f g h i z w v x.1

include hz hw

/-- The actual weighted original-label sum, grouped into literal image-prime fibres.
All nonminimal image contributions are proved zero using the actual remaining ideal. -/
theorem finsum_originalExteriorLabels_eq_finsum_imagePrimes {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v x₀))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v x₀) = Ideal.span (Set.range s)) :
    (∑ᶠ η : L,
      (correspondenceIncidenceTorCoefficient K f g h z w
        (correspondenceLeftExteriorGenericLabel f g h i z w v η.1) *
          (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
        ((q').residueDegree η.1.1 : ℤ) *
          Koszul.seqEuler (fun j => α (s j))
            (R ⧸ (correspondenceRemainingOriginalImagePrime f g h i z w v x.1 η).asIdeal)) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        ∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1},
          (correspondenceIncidenceTorCoefficient K f g h z w
            (correspondenceLeftExteriorGenericLabel f g h i z w v η.1) *
              (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
            ((q').residueDegree η.1.1 : ℤ) *
              Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal) := by
  classical
  let := finite_correspondenceRemainingOriginalGenericLabels f g h i z w v x.1 hz hw
  let : Fintype L := Fintype.ofFinite L
  let σ := correspondenceRemainingOriginalImagePrime f g h i z w v x.1
  let χ : PrimeSpectrum R → ℤ := fun p =>
    Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.asIdeal)
  let c : genericPoints E → ℤ := fun η =>
    (correspondenceIncidenceTorCoefficient K f g h z w
      (correspondenceLeftExteriorGenericLabel f g h i z w v η) *
        (correspondenceLeftExteriorFiberLength f g h i z w v η.1 : ℤ)) *
      ((q').residueDegree η.1 : ℤ)
  let a : L → ℤ := fun η => c η.1 * χ (σ η)
  let B : PrimeSpectrum R → ℤ := fun p =>
    ∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p}, c η.1 * χ p
  let hP := PrimeSpectrum.finite_setOfPred_isMin R
  let P := hP.toFinset
  have hB (p : PrimeSpectrum R) : B p = ∑ η ∈ Finset.univ with σ η = p, a η := by
    have hfibre : B p = ∑ᶠ η : {η : L // σ η = p}, a η.1 := by
      let e := correspondenceRemainingOriginalImagePrimeFiberEquiv f g h i z w v x.1 p
      apply finsum_eq_of_bijective e.symm e.symm.bijective
      intro η
      change c η.1 * χ p = c (e.symm η).1.1 * χ (σ (e.symm η).1)
      have hσ : σ (e.symm η).1 = p := (e.symm η).2
      have hη : (e.symm η).1.1 = η.1 := rfl
      exact (congrArg₂ (fun a b : ℤ => a * b) (congrArg c hη) (congrArg χ hσ)).symm
    rw [hfibre, finsum_subtype_eq_finsum_cond (f := a)]
    apply finsum_cond_eq_sum_of_cond_iff
    intro η _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (∑ᶠ η : L, a η) = ∑ᶠ p : {p : PrimeSpectrum R // IsMin p}, B p.1
  rw [finsum_eq_sum_of_fintype, finsum_subtype_eq_finsum_cond (f := B)]
  change (∑ η : L, a η) = ∑ᶠ p ∈ {p : PrimeSpectrum R | IsMin p}, B p
  rw [finsum_mem_eq_finite_toFinset_sum B hP]
  change (∑ η : L, a η) = ∑ p ∈ P, B p
  have hI := isIdealOfDefinition_correspondenceRemainingImageMiddleList
    f g h i z w v x s hs
  symm
  calc
    _ = ∑ p ∈ P, ∑ η ∈ Finset.univ with σ η = p, a η :=
      Finset.sum_congr rfl fun p _ => hB p
    _ = ∑ η ∈ Finset.univ with σ η ∈ P, a η :=
      Finset.sum_fiberwise_eq_sum_filter Finset.univ P σ a
    _ = ∑ η : L, a η := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro η hη hn
      have hp : ¬ IsMin (σ η) := fun hp =>
        hn (Finset.mem_filter.mpr ⟨hη, hP.mem_toFinset.mpr hp⟩)
      have hz := Koszul.seqEuler_quotient_eq_zero_of_not_isMin
        (fun j => α (s j)) hI (σ η) hp
      change c η.1 * Koszul.seqEuler (fun j => α (s j)) (R ⧸ (σ η).asIdeal) = 0
      rw [hz, mul_zero]

end Stacks.Chow

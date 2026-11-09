/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFixedLabelEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycle

/-!
# The actual signed first Tor coefficients in weighted remaining Euler

Sum the proved fixed-original-label equality with the actual original pair Tor
coefficient. The finite generic first-incidence set comes from the actual smooth
middle geometry. The image-stalk minimal primes and the actual finite exterior
fibres are finite as well. Thus the sums can be interchanged without any global
quasi-compactness or uniform dimension assumption.

The first Tor coefficient is the existing alternating sum of the actual Tor
lengths, not a fundamental-cycle weight. Every original exterior label retains
its original first label, full closed-fibre multiplicity, and finite-map residue
degree. The left coefficients are exactly the original Tor coefficient times
the original incidence-map residue degree used by `WeightedPairing`.

This local equality still needs the actual whole finite Tor family's geometric
localization identity and the remaining pair-Tor identification before it yields
a global weighted remaining-cycle comparison.
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

local notation3 (prettyPrint := false) "E" =>
  correspondenceLeftIntermediateSupportProduct f g h i z w v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "I₀" => correspondenceIncidence f g h z w
local notation3 (prettyPrint := false) "q'" =>
  correspondenceLeftIntermediateImageMap f g h i z w v
local notation3 (prettyPrint := false) "π" => correspondenceLeftExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" =>
  (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)

variable (x : correspondenceLeftImageIncidence f g h i z w v)

local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x

omit [Smooth f] [Smooth h] [IsSeparated g] in
/-- Actual signed first Tor coefficients and original residue weights, with every original
exterior generic label retained after finite regrouping. -/
theorem sum_firstTorCoefficient_mul_seqEuler_correspondenceRemainingImageComponentStalk
    [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hx : x ∈ genericPoints (correspondenceLeftImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v x₀))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v x₀) = Ideal.span (Set.range s)) :
    let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
    (∑ t : genericPoints I₀,
      (correspondenceIncidenceTorCoefficient K f g h z w t *
        ((correspondenceIncidenceMap f g h z w).residueDegree t.1 : ℤ)) *
          Koszul.seqEuler (fun j => α (s j))
            (correspondenceRemainingImageComponentStalk f g h i z w v x t.1)) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        ∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1},
          (correspondenceIncidenceTorCoefficient K f g h z w
            (correspondenceLeftExteriorGenericLabel f g h i z w v η.1) *
              (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
            ((q').residueDegree η.1.1 : ℤ) *
              Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal) := by
  classical
  let := isFinite_correspondenceLeftIntermediateImageMap f g h i z w v hz hw
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceLeftImageExteriorProjection f g h i z w v ≫ sJ)
  let := (finite_genericPoints_correspondenceIncidence_of_smooth f g h z w hw).fintype
  let P := {p : PrimeSpectrum R // IsMin p}
  let : Fintype P := (PrimeSpectrum.finite_setOfPred_isMin R).fintype
  let Q (p : P) := {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1}
  let (p : P) : Fintype (Q p) :=
    (((q').finite_preimage_singleton ((T).fromSpecStalk x₀ p.1)).preimage
      Subtype.val_injective.injOn).fintype
  let c : genericPoints I₀ → ℤ := correspondenceIncidenceTorCoefficient K f g h z w
  let χ : P → ℤ := fun p => Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal)
  let b (p : P) (η : Q p) : ℤ :=
    (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ) *
      ((q').residueDegree η.1.1 : ℤ)
  have H (t : genericPoints I₀) :
      ((correspondenceIncidenceMap f g h z w).residueDegree t.1 : ℤ) *
          Koszul.seqEuler (fun j => α (s j))
            (correspondenceRemainingImageComponentStalk f g h i z w v x t.1) =
        ∑ p : P, (∑ η : Q p, if π η.1.1 = t.1 then b p η else 0) * χ p := by
    have Ht := residueDegree_mul_seqEuler_correspondenceRemainingImageComponentStalk
      K f g h i z w v x t.1 hz hw hx s hs
    rw [correspondenceIncidenceToImage_residueDegree] at Ht
    simpa only [finsum_eq_sum_of_fintype] using Ht
  have hsingle (p : P) (η : Q p) :
      (∑ t : genericPoints I₀, c t * (if π η.1.1 = t.1 then b p η else 0)) =
        c (correspondenceLeftExteriorGenericLabel f g h i z w v η.1) * b p η := by
    let a := correspondenceLeftExteriorGenericLabel f g h i z w v η.1
    rw [Finset.sum_eq_single a]
    · simp only [a, correspondenceLeftExteriorGenericLabel, ite_true]
    · intro t _ hta
      have hne : π η.1.1 ≠ t.1 := fun ht => hta (Subtype.ext ht.symm)
      simp only [ite_eq_right hne, mul_zero]
    · simp
  calc
    _ = ∑ t : genericPoints I₀, c t *
        (∑ p : P, (∑ η : Q p, if π η.1.1 = t.1 then b p η else 0) * χ p) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [mul_assoc, H t]
    _ = ∑ p : P, ∑ η : Q p,
        (∑ t : genericPoints I₀, c t * (if π η.1.1 = t.1 then b p η else 0)) * χ p := by
      simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ = ∑ p : P, ∑ η : Q p,
        c (correspondenceLeftExteriorGenericLabel f g h i z w v η.1) * b p η * χ p := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro η _
      rw [hsingle]
    _ = _ := by
      change (∑ p : P, ∑ η : Q p,
        c (correspondenceLeftExteriorGenericLabel f g h i z w v η.1) * b p η * χ p) =
        ∑ᶠ p : P, ∑ᶠ η : Q p,
          (c (correspondenceLeftExteriorGenericLabel f g h i z w v η.1) *
            (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
              ((q').residueDegree η.1.1 : ℤ) * χ p
      rw [finsum_eq_sum_of_fintype]
      apply Finset.sum_congr rfl
      intro p _
      rw [finsum_eq_sum_of_fintype]
      apply Finset.sum_congr rfl
      intro η _
      simp only [b, mul_assoc]

end Stacks.Chow

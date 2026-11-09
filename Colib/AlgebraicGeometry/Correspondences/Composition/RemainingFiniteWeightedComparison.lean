/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWeightedCycleEuler

/-!
# The weighted remaining cycle and every maximal localization of the actual Tor family

At a generic point of the whole remaining image incidence, the coefficient of the actual
weighted remaining cycle is the residue-degree-weighted sum of the signed remaining Koszul
Euler characteristics of every maximal localization of the actual whole finite Tor family.
The family is the existing global sections of the original exterior Tor sheaves on the
full finite model. It is not an input and is never replaced by its degree-zero module.

The finite-algebra formula uses all maximal ideals of the original finite algebra. The
algebra may be nonlocal, nonreduced and nonflat over the actual image stalk. The original
remaining list is regular only in its original middle-pair stalk. Its genuine geometric
ideal of definition proves finite length before any conversion from extended naturals.
The first degree has its actual uniform module-vanishing bound, so the signed all-degree
finsums do not rely on cancellation or an unspecified cutoff.

This closes the finite-pushforward step between `RemainingWeightedCycleEuler` and the
local coefficient comparison. It does not identify these localized Euler characteristics
with combined-diagonal triple Tor, or assert global cycle equality or associativity.

## References

* Stacks Project, Tag 02M0: length under a finite map, as consumed by
  `Module.finiteAlgebra_length_eq_sum` and the genuine Koszul projection formula in
  `Koszul.sum_signed_seqEuler_restrictScalars_eq_sum`.
* Stacks Project, Tag 02R4: the residue-field degree in finite cycle pushforward.
* Independent motivic revision `a6805c4a87cdfd7717dd7a94039246a167f15380`,
  `Correspondences/Composition/Cycles/FirstStageWeightedRemainingCoefficient.lean`,
  blob `3ae09238bac659f48c9e4beb21004af8f02ffd84`: the finite-algebra local coefficient
  passage. The native family, projection formula and original-label weighted-cycle
  assembly are used here in place of the old recursive complex implementation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)

include hz hw

section LocalImage

variable [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]

/-- A finite window of the actual first-Tor family, localized at every maximal label.
No local module, finite length or scalar comparison is supplied by the caller. -/
theorem sum_signed_seqEuler_correspondenceRemainingFiniteTorModule_maximal
    (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))
    {r : ℕ} (s : Fin r → ((pullback h h).presheaf.stalk (correspondenceLeftImageMiddlePair f g h i z
        w v (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)))) (hsr : IsRegular
        ((pullback h h).presheaf.stalk (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v (correspondenceLeftImageIncidenceInclusion f
          g h i z w v x.1)) = Ideal.span (Set.range s))
    (J : Finset ℕ) :
    let R := correspondenceRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    letI := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
    ∑ b ∈ J, (-1 : ℤ) ^ b * Koszul.seqEuler (fun j => α (s j))
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ q : MaximalSpectrum B,
        (∑ b ∈ J, (-1 : ℤ) ^ b *
          Koszul.seqEuler
            (fun j => algebraMap B (Localization.AtPrime q.asIdeal)
              (algebraMap R B (α (s j))))
            (Localization.AtPrime q.asIdeal ⊗[B] M b)) *
              (Module.finiteAlgebraResidueDegree R B q : ℤ) := by
  dsimp only
  let T := correspondenceLeftIntermediateImageProduct f g h i z w v
  let R := correspondenceRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRemainingFiniteRing f g h i z w v x.1
  let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
  let M := correspondenceRemainingFiniteTorModule f g h i z w v x.1
  classical
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  let := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
  let : IsLocallyNoetherian (correspondenceIntersectionAmbient f g h) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceIntersectionAmbientToField K f g h)
  let := finite_maximalSpectrum_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
  let := Fintype.ofFinite (MaximalSpectrum B)
  rw [finsum_eq_sum_of_fintype]
  exact Koszul.sum_signed_seqEuler_restrictScalars_eq_sum (fun j => α (s j)) M J
    (fun b _ n => length_correspondenceRemainingFiniteTorKoszul_ne_top
      f g h i z w v hz hw x s hsr hs b n)

/-- The complete signed family localizes over all maximal ideals of the same whole algebra.
The cutoff is removed using actual module vanishing, including after tensor localization. -/
theorem finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_maximal
    (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))
    {r : ℕ} (s : Fin r → ((pullback h h).presheaf.stalk (correspondenceLeftImageMiddlePair f g h i z
        w v (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)))) (hsr : IsRegular
        ((pullback h h).presheaf.stalk (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v (correspondenceLeftImageIncidenceInclusion f
          g h i z w v x.1)) = Ideal.span (Set.range s)) :
    let R := correspondenceRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    letI := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b * Koszul.seqEuler (fun j => α (s j))
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ q : MaximalSpectrum B,
        (∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
          Koszul.seqEuler
            (fun j => algebraMap B (Localization.AtPrime q.asIdeal)
              (algebraMap R B (α (s j))))
            (Localization.AtPrime q.asIdeal ⊗[B] M b)) *
              (Module.finiteAlgebraResidueDegree R B q : ℤ) := by
  dsimp only
  let T := correspondenceLeftIntermediateImageProduct f g h i z w v
  let R := correspondenceRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRemainingFiniteRing f g h i z w v x.1
  let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
  let M := correspondenceRemainingFiniteTorModule f g h i z w v x.1
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  let := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
  obtain ⟨d, hd⟩ := exists_correspondenceRemainingFiniteTorModule_degreeBound
    K f g h i z w v hz hw x.1
  have hleft : (∑ᶠ b : ℕ, (-1 : ℤ) ^ b * Koszul.seqEuler (fun j => α (s j))
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b))) =
      ∑ b ∈ Finset.range (d + 1), (-1 : ℤ) ^ b * Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) := by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    by_contra hbd
    let : Subsingleton ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) := by
      change Subsingleton (M b)
      exact ModuleCat.isZero_iff_subsingleton.mp (hd b (lt_of_not_ge hbd))
    apply hb
    have hzero := Koszul.seqEuler_eq_zero_of_subsingleton
      (fun j => α (s j)) ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b))
    exact (congrArg (fun a => (-1 : ℤ) ^ b * a) hzero).trans (mul_zero _)
  have hright (q : MaximalSpectrum B) :
      (∑ᶠ b : ℕ, (-1 : ℤ) ^ b * Koszul.seqEuler
        (fun j => algebraMap B (Localization.AtPrime q.asIdeal)
          (algebraMap R B (α (s j))))
        (Localization.AtPrime q.asIdeal ⊗[B] M b)) =
      ∑ b ∈ Finset.range (d + 1), (-1 : ℤ) ^ b * Koszul.seqEuler
        (fun j => algebraMap B (Localization.AtPrime q.asIdeal)
          (algebraMap R B (α (s j))))
        (Localization.AtPrime q.asIdeal ⊗[B] M b) := by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    by_contra hbd
    let := ModuleCat.isZero_iff_subsingleton.mp (hd b (lt_of_not_ge hbd))
    apply hb
    have hzero := Koszul.seqEuler_eq_zero_of_subsingleton
      (fun j => algebraMap B (Localization.AtPrime q.asIdeal)
        (algebraMap R B (α (s j)))) (Localization.AtPrime q.asIdeal ⊗[B] M b)
    exact (congrArg (fun a => (-1 : ℤ) ^ b * a) hzero).trans (mul_zero _)
  refine hleft.trans ((sum_signed_seqEuler_correspondenceRemainingFiniteTorModule_maximal
    K f g h i z w v hz hw x s hsr hs (Finset.range (d + 1))).trans ?_)
  apply finsum_congr
  intro q
  exact congrArg (fun a : ℤ => a * (Module.finiteAlgebraResidueDegree R B q : ℤ))
    (hright q).symm

end LocalImage

/-- The literal weighted remaining-cycle coefficient is the complete signed sum over all
maximal localizations of the actual whole Tor family, with their actual residue degrees. -/
theorem correspondenceLeftWeightedRemainingCycle_eq_finsum_maximalEuler
    (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))
    [Smooth i] (hv : IsFiniteCorrespondencePoint h i v)
    [LocallyOfFiniteType (correspondenceIntermediateImageTarget f g h z w ≫ h)] [LocallyOfFiniteType
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    {r : ℕ} (s : Fin r → ((pullback h h).presheaf.stalk (correspondenceLeftImageMiddlePair f g h i z
        w v (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)))) (hsr : IsRegular
        ((pullback h h).presheaf.stalk (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v (correspondenceLeftImageIncidenceInclusion f
          g h i z w v x.1)) = Ideal.span (Set.range s)) :
    let R := correspondenceRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    letI := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
    correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv x.1 =
      ∑ᶠ q : MaximalSpectrum B,
        (∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
          Koszul.seqEuler
            (fun j => algebraMap B (Localization.AtPrime q.asIdeal)
              (algebraMap R B (α (s j))))
            (Localization.AtPrime q.asIdeal ⊗[B] M b)) *
              (Module.finiteAlgebraResidueDegree R B q : ℤ) := by
  dsimp only
  let T := correspondenceLeftIntermediateImageProduct f g h i z w v
  let R := correspondenceRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRemainingFiniteRing f g h i z w v x.1
  let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
  let M := correspondenceRemainingFiniteTorModule f g h i z w v x.1
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  let := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
  let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceLeftImageExteriorProjection f g h i z w v ≫
        (correspondenceIntermediateImageTarget f g h z w ≫ h))
  exact (finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedCycle
    K f g h i z w v hz hw hv x s hsr hs).symm.trans
      (finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_maximal
        K f g h i z w v hz hw x s hsr hs)

end Stacks.Chow

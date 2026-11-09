/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorBound
public import Colib.RingTheory.Koszul.GenericFiniteReindex
public import Colib.RingTheory.Koszul.FinitePushforwardRegular
public import Colib.RingTheory.Koszul.EulerVanishing

/-!
# Two genuine finite-algebra Euler expansions for the whole right Tor family

The coefficient family is the global sections of the actual G,H exterior Tor sheaves
on the actual whole finite model. The remaining list is in the original Y self-product.
Generic right-image support proves its ideal of definition. Thus every remaining
homology has finite length before converting extended naturals to integer coefficients.

The same native finite-algebra projection formula gives both minimal-prime devissage
and the maximal-localization sum. The latter is extended to all original Tor degrees
using actual module vanishing on the entire finite model. Every maximal label and its
native residue-field degree remains present. No coefficient comparison or flatness of
the finite image map is assumed. Flatness used for the bound is only over the base field.

References: Stacks 02M0, 02M1 (finite and flat-local length) and 02R4 (cycle degrees).
Compare motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean,
blob 5771cc85d24a32f3610872f2a94d457154d1673b, lines 107-213. The image-component
replacement and the reindexing as actual triple fibre points are separate obligations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i]
  [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)

include hz hw hv

/-- Actual generic support proves finite length for each remaining homology degree. -/
theorem length_correspondenceRightRemainingFiniteTorKoszul_ne_top
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    {r : ℕ} (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hsr : RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) (b n : ℕ) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    Module.length B
      ((Koszul.seqComplexTensor (fun j => algebraMap R B (α (s j))) (M b)).homology n) ≠ ⊤ := by
  dsimp only
  let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
  let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  let := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x.1
  let : IsLocallyNoetherian (correspondenceIntersectionAmbient g h i) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceIntersectionAmbientToField K g h i)
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g)
  let := isLocallyNoetherian_correspondenceRightIntermediateImageProduct f g h i z w v hz hw hv
  let := moduleFinite_correspondenceRightRemainingFiniteTorModule f g h i z w v hw hv x.1 b
  let := α.toAlgebra
  exact Koszul.length_seqComplexTensor_finiteAlgebra_ne_top_of_isRegular s hsr (M b)
    (isIdealOfDefinition_correspondenceRightRemainingImageMiddleList f g h i z w v x s hs) n

/-- Full minimal-prime devissage for the actual original Tor modules in a finite degree window. -/
theorem sum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_minimal
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    {r : ℕ} (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) (J : Finset ℕ) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    ∑ b ∈ J, (-1 : ℤ) ^ b * Koszul.seqEuler (fun j => α (s j))
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ q : {q : PrimeSpectrum B // IsMin q},
        (∑ b ∈ J, (-1 : ℤ) ^ b *
          ((Module.length (Localization.AtPrime q.1.asIdeal)
            (LocalizedModule q.1.asIdeal.primeCompl (M b))).toNat : ℤ)) *
              (Stacks.Length.primeResidueDegree (algebraMap R B)
                (q.1.asIdeal.comap (algebraMap R B)) q.1.asIdeal : ℤ) *
                  Koszul.seqEuler (fun j => α (s j))
                    (R ⧸ q.1.asIdeal.comap (algebraMap R B)) := by
  dsimp only
  let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
  let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  let := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x.1
  let : IsLocallyNoetherian (correspondenceIntersectionAmbient g h i) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceIntersectionAmbientToField K g h i)
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g)
  let := isLocallyNoetherian_correspondenceRightIntermediateImageProduct f g h i z w v hz hw hv
  let : ∀ b, Module.Finite B (M b) :=
    fun b => moduleFinite_correspondenceRightRemainingFiniteTorModule f g h i z w v hw hv x.1 b
  exact Koszul.sum_signed_seqEuler_restrictScalars_eq_finsum_minimalSourcePrimes
    (fun j => α (s j)) M
    (isIdealOfDefinition_correspondenceRightRemainingImageMiddleList f g h i z w v x s hs) J

/-- Finite-pushforward Euler uses every maximal localization of the original whole algebra. -/
theorem sum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_maximal
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    {r : ℕ} (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hsr : RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) (J : Finset ℕ) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    letI := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x.1
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
  let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
  let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  let := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x.1
  classical
  let := finite_maximalSpectrum_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x.1
  let := Fintype.ofFinite (MaximalSpectrum B)
  rw [finsum_eq_sum_of_fintype]
  exact Koszul.sum_signed_seqEuler_restrictScalars_eq_sum (fun j => α (s j)) M J
    (fun b _ n => length_correspondenceRightRemainingFiniteTorKoszul_ne_top
      K f g h i z w v hz hw hv x s hsr hs b n)

/-- All original Tor degrees are retained; the cutoff is removed by actual module vanishing. -/
theorem finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_maximal
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    {r : ℕ} (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hsr : RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    letI := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x.1
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
  let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
  let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  let := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x.1
  obtain ⟨d, hd⟩ := exists_correspondenceRightRemainingFiniteTorModule_degreeBound
    K f g h i z w v hw hv x.1
  have hleft : (∑ᶠ b : ℕ, (-1 : ℤ) ^ b * Koszul.seqEuler (fun j => α (s j))
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b))) =
      ∑ b ∈ Finset.range (d + 1), (-1 : ℤ) ^ b * Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) := by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    change b ∈ Finset.range (d + 1)
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
    change b ∈ Finset.range (d + 1)
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    by_contra hbd
    let := ModuleCat.isZero_iff_subsingleton.mp (hd b (lt_of_not_ge hbd))
    apply hb
    have hzero := Koszul.seqEuler_eq_zero_of_subsingleton
      (fun j => algebraMap B (Localization.AtPrime q.asIdeal)
        (algebraMap R B (α (s j)))) (Localization.AtPrime q.asIdeal ⊗[B] M b)
    exact (congrArg (fun a => (-1 : ℤ) ^ b * a) hzero).trans (mul_zero _)
  refine hleft.trans ((sum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_maximal
    K f g h i z w v hz hw hv x s hsr hs (Finset.range (d + 1))).trans ?_)
  apply finsum_congr
  intro q
  exact congrArg (fun a : ℤ => a * (Module.finiteAlgebraResidueDegree R B q : ℤ))
    (hright q).symm

end Stacks.Chow

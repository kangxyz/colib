/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleGenericImageSupport
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleGenericSupport
public import Colib.AlgebraicGeometry.Chow.GenericPushforward

/-!
# The native cycle of the actual combined-diagonal triple Tor

Actual triple generics form a finite set by finite incidence geometry. Their coefficients
are the alternating lengths of native Tor of the full exterior support and full fourfold
local rings over the original sixfold local ring. The actual three-ideal radical gives
finite lengths, including zero modules. Regularity gives the actual local dimension bound.
Thus neither `ENat.toNat` nor `finsum` silently discards an infinite value.

The cycle is Mathlib's native `AlgebraicCycle`, assembled on actual generic points. Its
finite pushforward uses every original residue degree and all coincident fibre labels.
The generic-image theorem, not a support premise, proves zero coefficients at nongeneric
whole-image points. No comparison with a weighted remaining cycle is used in this file.

References: Stacks 0AZ4 (finite Tor), 00L5 (finite length from closed-point support),
0AZT (Tor multiplicity), 02QR (cycles), 02R4 (finite pushforward). Implementation context:
independent motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/FirstStageWeightedRemainingCoefficient.lean, lines 169-245, and
Composition/Cycles/LeftComposition.lean, lines 155-219.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]

/-- Every actual combined-diagonal triple Tor length is finite at an original generic point. -/
theorem correspondenceTripleIncidenceTor_length_ne_top
    (t : genericPoints (correspondenceTripleIncidence f g h i z w v)) (n : ℕ) :
    Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v t.1)
      (correspondenceTripleIncidenceTor f g h i z w v t.1 n) ≠ ⊤ := by
  let : IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceSixfoldAmbientToField K f g h i)
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v t.1
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v t.1
  let N := correspondenceTripleIncidenceFourfoldStalkModule f g h i z w v t.1
  let B := (correspondenceFourfoldProduct f g h i).presheaf.stalk
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t.1)
  let ψ := ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t.1)).hom
  let : Module.Finite A N := RingHom.Finite.of_surjective ψ
    (SurjectiveOnStalks.stalkMap_surjective (correspondenceFourfoldDiagonalInclusion f g h i) _)
  let : Module.Finite A (correspondenceTripleIncidenceTor f g h i z w v t.1 n) :=
    tor_finite_of_noetherian A M N n
  apply Module.length_ne_top_iff.mpr
  apply isFiniteLength_of_support_subset
  intro q hq
  have hq' := Module.mem_support_iff_of_finite.mp hq
  have hM' : Module.annihilator A M ≤ q.asIdeal := by
    intro a ha
    exact hq' (mem_annihilator_tor_of_mem_annihilator M N n ha)
  rw [correspondenceTripleIncidenceSupportStalkModule_annihilator] at hM'
  have hN' : RingHom.ker ψ ≤ q.asIdeal := by
    obtain ⟨eTor⟩ := tor_symm_canonically_iso A n
    let eSwap : correspondenceTripleIncidenceTor f g h i z w v t.1 n ≅
        ((Tor (ModuleCat A) n).obj N).obj M := (eTor.app M).app N
    intro a ha
    apply hq'
    apply mem_annihilator_of_moduleCat_iso eSwap.symm
    apply mem_annihilator_tor_of_mem_annihilator N M n
    exact ModuleCat.ker_le_annihilator_restrictScalars ψ (ModuleCat.of B B) ha
  change RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t.1)).hom ≤ _ at hN'
  rw [ker_stalkMap_eq_idealStalk_ker] at hN'
  change IdealSheafData.stalk
    (correspondenceSecondDiagonalInclusion f g h i ≫
      correspondenceFirstDiagonalInclusion f g h i).ker
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v t.1) ≤ _ at hN'
  rw [ker_correspondenceFourfoldDiagonal, IdealSheafData.stalk_sup, sup_le_iff] at hN'
  have hsum : correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v t.1 ≤
      q.asIdeal := sup_le hN'.1 (sup_le hN'.2 hM')
  have hmax : IsLocalRing.maximalIdeal A ≤ q.asIdeal := by
    rw [← radical_correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v t]
    exact q.isPrime.radical_le_iff.mpr hsum
  exact Set.mem_singleton_iff.mpr
    (PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) hmax))

/-- The integer conversion retains the full actual finite Tor length. -/
theorem natCast_toNat_length_correspondenceTripleIncidenceTor
    (t : genericPoints (correspondenceTripleIncidence f g h i z w v)) (n : ℕ) :
    ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v t.1)
      (correspondenceTripleIncidenceTor f g h i z w v t.1 n)).toNat : ℕ∞) =
      Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v t.1)
        (correspondenceTripleIncidenceTor f g h i z w v t.1 n) :=
  ENat.natCast_toNat (correspondenceTripleIncidenceTor_length_ne_top K f g h i z w v t n)

/-- Actual combined-diagonal Tor vanishes above the original local dimension. -/
theorem isZero_correspondenceTripleIncidenceTor_of_lt
    (t : correspondenceTripleIncidence f g h i z w v) (n : ℕ)
    (hn : correspondenceTripleIncidenceTorDegreeBound K f g h i z w v t < n) :
    IsZero (correspondenceTripleIncidenceTor f g h i z w v t n) := by
  let := isRegularLocalRing_correspondenceSixfoldAmbient_stalk K f g h i
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v t)
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v t
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v t
  have hcriterion : IsRegularLocalRing A ↔
      (⨆ N : ModuleCat.{u} A, projectiveDimension N) = ringKrullDim A :=
    (isRegularLocalRing_tfae (R := A)).out 3 4
  have hpd : HasProjectiveDimensionLE M
      (correspondenceTripleIncidenceTorDegreeBound K f g h i z w v t) := by
    rw [← projectiveDimension_le_iff]
    calc
      projectiveDimension M ≤ ⨆ N : ModuleCat.{u} A, projectiveDimension N :=
        le_iSup (fun N : ModuleCat.{u} A => projectiveDimension N) M
      _ = ringKrullDim A := hcriterion.mp inferInstance
      _ = (correspondenceTripleIncidenceTorDegreeBound K f g h i z w v t : WithBot ℕ∞) :=
        ringKrullDim_eq_correspondenceTripleIncidenceTorDegreeBound K f g h i z w v t
  exact StacksDraft.ProjectiveDimension.isZero_Tor_of_hasProjectiveDimensionLE M
    (correspondenceTripleIncidenceFourfoldStalkModule f g h i z w v t) _ n hpd hn

/-- Only finitely many signed actual Tor terms are nonzero. -/
theorem finite_support_correspondenceTripleIncidenceTorTerm
    (t : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    (Function.support fun n : ℕ => (-1 : ℤ) ^ n *
      ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v t.1)
        (correspondenceTripleIncidenceTor f g h i z w v t.1 n)).toNat : ℤ)).Finite := by
  refine (Set.finite_Iic
    (correspondenceTripleIncidenceTorDegreeBound K f g h i z w v t.1)).subset ?_
  intro n hn
  apply le_of_not_gt
  intro hlt
  have hzero : Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v t.1)
      (correspondenceTripleIncidenceTor f g h i z w v t.1 n) = 0 :=
    Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
      (isZero_correspondenceTripleIncidenceTor_of_lt K f g h i z w v t.1 n hlt))
  exact hn (by simp only [hzero, ENat.toNat_zero, Nat.cast_zero, mul_zero])

/-- The genuine finite alternating coefficient of the original full triple Tor. -/
def correspondenceTripleIncidenceTorCoefficient
    (t : genericPoints (correspondenceTripleIncidence f g h i z w v)) : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
    ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v t.1)
      (correspondenceTripleIncidenceTor f g h i z w v t.1 n)).toNat : ℤ)

/-- The native actual triple-Tor cycle, with no reduction or chosen coefficient family. -/
def correspondenceTripleIncidenceTorCycle
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    AlgebraicCycle (correspondenceTripleIncidence f g h i z w v) ℤ :=
  AlgebraicCycle.ofGenericCoefficients
    (finite_genericPoints_correspondenceTripleIncidence_of_smooth f g h i z w v hw hv)
    (correspondenceTripleIncidenceTorCoefficient K f g h i z w v)

/-- At an original generic label the coefficient is the full signed actual Tor sum. -/
@[simp]
theorem correspondenceTripleIncidenceTorCycle_apply_generic
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (t : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv t.1 =
      correspondenceTripleIncidenceTorCoefficient K f g h i z w v t :=
  AlgebraicCycle.ofGenericCoefficients_apply_generic _ _ t

/-- The actual triple cycle has support only at original generic points. -/
theorem support_correspondenceTripleIncidenceTorCycle_subset
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv).support ⊆
      genericPoints (correspondenceTripleIncidence f g h i z w v) :=
  AlgebraicCycle.support_ofGenericCoefficients_subset _ _

/-- The pushed actual triple cycle vanishes at nongeneric whole-image points by its
proved actual source geometry, not by a caller-supplied support condition. -/
theorem tripleTorPushforward_eq_zero_of_not_generic
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (hx : x ∉ genericPoints (correspondenceLeftImageIncidence f g h i z w v)) :
    letI := isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw
    finiteCyclePushforward (correspondenceTripleToLeftImageIncidence f g h i z w v)
      (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) x = 0 := by
  let := isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw
  by_contra hne
  obtain ⟨t, ht, htx⟩ := finiteCyclePushforward_support_subset
    (correspondenceTripleToLeftImageIncidence f g h i z w v)
    (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) hne
  apply hx
  rw [← htx]
  exact mem_genericPoints_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw hv t
    (support_correspondenceTripleIncidenceTorCycle_subset K f g h i z w v hw hv ht)

/-- The actual pushed generic coefficient retains every original triple-fibre label and
its own residue degree. This identifies the literal endpoint of the preceding Euler join. -/
theorem tripleTorPushforward_apply_generic
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v)) :
    letI := isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw
    finiteCyclePushforward (correspondenceTripleToLeftImageIncidence f g h i z w v)
        (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) x.1 =
      ∑ᶠ t : {t : genericPoints (correspondenceTripleIncidence f g h i z w v) //
        correspondenceTripleToLeftImageIncidence f g h i z w v t.1 = x.1},
        (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v t.1.1)
            (correspondenceTripleIncidenceTor f g h i z w v t.1.1 n)).toNat : ℤ)) *
          ((correspondenceTripleToLeftImageIncidence f g h i z w v).residueDegree t.1.1 : ℤ) := by
  let p := correspondenceTripleToLeftImageIncidence f g h i z w v
  let := isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw
  let e : {t : correspondenceTripleIncidence f g h i z w v // p t = x.1} ≃
      {t : genericPoints (correspondenceTripleIncidence f g h i z w v) // p t.1 = x.1} :=
    { toFun := fun t => ⟨⟨t.1,
        mem_genericPoints_of_finite_image p t.1 (t.2.symm ▸ x.2)⟩, t.2⟩
      invFun := fun t => ⟨t.1.1, t.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [finiteCyclePushforward_apply, ← finsum_set_coe_eq_finsum_mem]
  apply finsum_eq_of_bijective e e.bijective
  intro t
  change correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv t.1 *
      (p.residueDegree t.1 : ℤ) =
    correspondenceTripleIncidenceTorCoefficient K f g h i z w v (e t).1 *
      (p.residueDegree t.1 : ℤ)
  rw [correspondenceTripleIncidenceTorCycle_apply_generic
    K f g h i z w v hw hv (e t).1]

end Stacks.Chow

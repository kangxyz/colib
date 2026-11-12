/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatDegree
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.RationalDivisor

/-!
# Laurent divisor calculation on the two torus graphs

This gives the degree calculation of Voevodsky, Cancellation theorem (2010),
Lemma 4.3, on the actual native torus over an affine source. The whole monic
polynomial quotient carries the generic lengths used by the cycle map. Its
projection has the rank given by the monic power basis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Polynomial
open Function.locallyFinsuppWithin Stacks.Chow
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

attribute [local instance] Classical.propDecidable

variable {A B : Scheme.{u}}

private def compactCyclePushforward (g : A ⟶ B) [QuasiCompact g] [CompactSpace A] :
    AlgebraicCycle A ℤ →+ AlgebraicCycle B ℤ where
  toFun := AlgebraicCycle.map g (fun _ : A ↦ (0 : ℕ)) (fun _ : B ↦ (0 : ℕ))
  map_zero' := by
    apply Function.locallyFinsuppWithin.ext
    intro y
    simp [AlgebraicCycle.map, AlgebraicCycle.mapCoeff]
  map_add' c d := by
    apply Function.locallyFinsuppWithin.ext
    intro y
    simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply,
      AlgebraicCycle.mapCoeff, ite_true, Function.locallyFinsuppWithin.coe_add,
      Pi.add_apply, add_mul]
    refine finsum_mem_add_distrib' (c.finite_support.subset ?_) (d.finite_support.subset ?_)
    · intro x hx
      exact (mul_ne_zero_iff.mp hx.2).1
    · intro x hx
      exact (mul_ne_zero_iff.mp hx.2).1

private theorem compactCyclePushforward_single (g : A ⟶ B) [QuasiCompact g] [CompactSpace A]
    (x : A) (n : ℤ) :
    compactCyclePushforward g (single x n) = single (g x) (n * (g.residueDegree x : ℤ)) := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro y
  change AlgebraicCycle.map g (fun _ : A ↦ (0 : ℕ)) (fun _ : B ↦ (0 : ℕ)) (single x n) y = _
  simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply,
    AlgebraicCycle.mapCoeff, ite_true]
  rw [← finsum_set_coe_eq_finsum_mem]
  by_cases hy : y = g x
  · subst y
    rw [finsum_eq_single _ ⟨x, by simp⟩]
    · simp
    · intro z hz
      have hzx : (z : A) ≠ x := fun h ↦ hz (Subtype.ext h)
      simp [single_apply, hzx]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    · simp [single_apply, hy]
    · intro z
      have hzx : (z : A) ≠ x := fun h ↦ Ne.symm hy (by simpa [h] using z.2)
      simp [single_apply, hzx]

variable {S : Scheme.{u}} {R : Type u} [CommRing R]

local instance torusStructure_quasiCompact :
    QuasiCompact (multiplicativeGroupBaseChange S ↘ S) := by
  change QuasiCompact (pullback.snd
    (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S))
  infer_instance

/-- The actual monic quotient has rank equal to the degree at every source point. -/
theorem projection_finrank_eq_natDegree [Nontrivial R] (p : R[X]) (hp : p.Monic)
    (x : Spec (.of R)) :
    (projection p).finrank x = p.natDegree := by
  let : Module.Free R (AdjoinRoot p) := hp.free_adjoinRoot
  let : Module.Finite R (AdjoinRoot p) := hp.finite_adjoinRoot
  rw [projection, ← AdjoinRoot.algebraMap_eq, Scheme.Hom.finrank_SpecMap_algebraMap]
  simpa only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id,
    AdjoinRoot.powerBasis'_dim] using (AdjoinRoot.powerBasis' hp).finrank

/-- Forgetting the torus coordinate of the native polynomial cycle retains the full
monic-quotient rank, including all multiplicities of repeated roots. -/
theorem polynomialCycle_map_projection [Nontrivial R] [IsNoetherianRing R]
    (f : Spec (.of R) ⟶ S) (p : R[X])
    (hp : p.Monic) (hu : IsUnit (p.coeff 0)) :
    AlgebraicCycle.map (pullback.fst f (multiplicativeGroupBaseChange S ↘ S))
      (fun _ : ambient f ↦ (0 : ℕ)) (fun _ : Spec (.of R) ↦ (0 : ℕ))
      (polynomialCycle f p hp hu).val =
      (p.natDegree : ℤ) • AlgebraicCycle.fundamentalCycle (Spec (.of R)) := by
  classical
  let π := pullback.fst f (multiplicativeGroupBaseChange S ↘ S)
  let : CompactSpace (ambient f) := QuasiCompact.compactSpace_of_compactSpace π
  let : IsNoetherian (Spec (.of (AdjoinRoot p))) := quotient_isNoetherian p
  let : IsFinite (projection p) := projection_isFinite p hp
  let : Flat (projection p) := projection_flat p hp
  let : IsClosedImmersion (inclusion f p hu) := inclusion_isClosedImmersion f p hu
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite
    (Spec (.of (AdjoinRoot p)))).fintype
  change compactCyclePushforward π (polynomialCycle f p hp hu).val = _
  calc
    _ = finiteCyclePushforward (projection p)
          (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot p)))) := by
      rw [polynomialCycle_eq_sum, map_sum, AlgebraicCycle.fundamentalCycle,
        finiteCyclePushforward_ofGenericCoefficients]
      apply Finset.sum_congr rfl
      intro x _
      have hproj : inclusion f p hu ≫ π = projection p := inclusion_fst f p hu
      have hpoint : π (inclusion f p hu x.val) = projection p x.val :=
        congrArg (fun g : Spec (.of (AdjoinRoot p)) ⟶ Spec (.of R) ↦ g x.val) hproj
      have hdegree : π.residueDegree (inclusion f p hu x.val) =
          (projection p).residueDegree x.val := by
        rw [← hproj, residueDegree_comp,
          residueDegree_eq_one_of_isPreimmersion (inclusion f p hu) x.val, mul_one]
      rw [compactCyclePushforward_single, hpoint, hdegree]
    _ = _ := finiteCyclePushforward_fundamentalCycle_of_constant_finrank
      (projection p) p.natDegree (projection_finrank_eq_natDegree p hp)

/-- The equation (t^n-1) as an actual monic denominator on the torus. -/
def powerSubOneDenominator (n : ℕ) (hn : n ≠ 0) : denominators R :=
  ⟨Polynomial.X ^ n - 1, monic_X_pow_sub_one hn, by simp [coeff_X_pow, Ne.symm hn]⟩

theorem powerSubOneDenominator_natDegree [Nontrivial R] (n : ℕ) (hn : n ≠ 0) :
    (powerSubOneDenominator (R := R) n hn).val.natDegree = n := by
  change ((Polynomial.X : R[X]) ^ n - 1).natDegree = n
  simpa only [map_one] using (natDegree_X_pow_sub_C (R := R) (n := n) (r := 1))

/-- On the identity graph the original denominator differs from the monic denominator
by the forward Laurent coordinate unit. -/
theorem identityGraphDenominator_toLaurent (n : ℕ) (hn : n ≠ 0) :
    toLaurent ((Polynomial.X : R[X]) ^ (n + 1) - Polynomial.X) =
      LaurentPolynomial.T 1 * toLaurent (powerSubOneDenominator (R := R) n hn).val := by
  rw [← toLaurent_X, ← map_mul]
  congr 1
  simp only [powerSubOneDenominator, pow_succ', mul_sub, mul_one]

variable [IsNoetherianRing R]

/-- The signed divisor on the identity graph after removing the Laurent coordinate unit. -/
def identityGraphDivisor (f : Spec (.of R) ⟶ S) (n : ℕ) (hn : n ≠ 0) :
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) :=
  rationalDivisor f (admissibleFraction (powerSubOneDenominator (n + 1) (Nat.succ_ne_zero _))
    (powerSubOneDenominator n hn))

/-- The identity graph gives one copy of the whole source fundamental cycle after
the two cuts and the actual projection of the signed Laurent divisor. -/
theorem identityGraphDivisor_map_projection [Nontrivial R] (f : Spec (.of R) ⟶ S)
    (n : ℕ) (hn : n ≠ 0) :
    AlgebraicCycle.map (pullback.fst f (multiplicativeGroupBaseChange S ↘ S))
      (fun _ : ambient f ↦ (0 : ℕ)) (fun _ : Spec (.of R) ↦ (0 : ℕ))
      (identityGraphDivisor f n hn).val = AlgebraicCycle.fundamentalCycle (Spec (.of R)) := by
  let π := pullback.fst f (multiplicativeGroupBaseChange S ↘ S)
  let : CompactSpace (ambient f) := QuasiCompact.compactSpace_of_compactSpace π
  let p := powerSubOneDenominator (R := R) (n + 1) (Nat.succ_ne_zero _)
  let q := powerSubOneDenominator (R := R) n hn
  change compactCyclePushforward π (rationalDivisor f (admissibleFraction p q)).val = _
  rw [rationalDivisor_fraction]
  change compactCyclePushforward π ((denominatorCycle f p).val - (denominatorCycle f q).val) = _
  rw [map_sub]
  change AlgebraicCycle.map π (fun _ : ambient f ↦ (0 : ℕ)) (fun _ : Spec (.of R) ↦ (0 : ℕ))
        (polynomialCycle f p.val p.property.1 p.property.2).val -
      AlgebraicCycle.map π (fun _ : ambient f ↦ (0 : ℕ)) (fun _ : Spec (.of R) ↦ (0 : ℕ))
        (polynomialCycle f q.val q.property.1 q.property.2).val = _
  rw [polynomialCycle_map_projection, polynomialCycle_map_projection,
    show p.val.natDegree = n + 1 from powerSubOneDenominator_natDegree _ _,
    show q.val.natDegree = n from powerSubOneDenominator_natDegree _ _]
  rw [sub_eq_add_neg, ← sub_zsmul, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_zsmul]

/-- The constant-one graph specializes the two cut equations to the same divisor. -/
theorem constantOneGraphDivisor_eq_zero (f : Spec (.of R) ⟶ S) (n : ℕ) :
    rationalDivisor f (admissibleFraction
      (powerSubOneDenominator (n + 1) (Nat.succ_ne_zero _))
      (powerSubOneDenominator (n + 1) (Nat.succ_ne_zero _))) = 0 := by
  rw [admissibleFraction_self, rationalDivisor_one]

end AlgebraicGeometry.NativeTorusPolynomial

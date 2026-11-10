/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.PowerBasis.TensorFactors
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenScalarBaseChange
public import Mathlib.FieldTheory.PrimitiveElement

import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Ring.CharZero

/-!
# Chosen finite norms under an actual full tensor decomposition

The actual tensor coordinates give power bases on the original factor fields.
Their minimal polynomials identify the full product index with the existing
literal coefficient-factor subtype. The accepted chosen scalar-factor formula
and the chosen comparison in those actual presentations give the sum of the
original factor norms, along the original coordinate ring maps.

The source is an arbitrary finite characteristic-zero field extension. The
coefficient extension is arbitrary, and no normality or prime-degree condition
is imposed on any field. Target finite-dimensionality is derived from the actual
coordinates. The final statements obtain their source power basis from the
native primitive element theorem, so callers supply no presentation.

All norm fields share the universe required by the native Stacks chosen norm.
There is no replacement norm, carrier, algebra action, or assumed norm square.
The formulas hold for the whole Milnor ring and every homogeneous degree,
including zero, both pointwise and as equalities of native additive maps.
-/

@[expose] public noncomputable section

open Polynomial UniqueFactorizationMonoid
open scoped TensorProduct

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

variable {F K E : Type u} [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra F E] [FiniteDimensional F E] [CharZero F]
  {ι : Type v} [Fintype ι] {D : ι → Type u}
  [∀ j, Field (D j)] [∀ j, Algebra K (D j)]

/-- The original chosen norm commutes with an actual full tensor decomposition,
using a supplied source power basis only to prove the coordinate factorization. -/
theorem milnorKNormRing_map_eq_sum_tensorProductPiEquiv_of_powerBasis
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (x : MilnorKRing E) :
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKRingMap (algebraMap F K) (milnorKNormRing F E x) =
      ∑ j, milnorKNormRing K (D j)
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) x) := by
  classical
  intro hFinite
  let hCharZero : CharZero K :=
    (RingHom.charZero_iff (algebraMap F K).injective).mp inferInstance
  let b (j : ι) : PowerBasis K (D j) :=
    Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)
  have hb (j : ι) : (b j).gen = ε (1 ⊗ₜ[F] pb.gen) j :=
    Classical.choose_spec (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)
  have hint (j : ι) : IsIntegral K (ε (1 ⊗ₜ[F] pb.gen) j) :=
    hb j ▸ (b j).isIntegral_gen
  let p : MonicIrreducibleOfDegree F (minpoly F pb.gen).natDegree :=
    minpolyOfDegree F pb.isIntegral_gen
  let q (j : ι) : MonicIrreducibleOfDegree K
      (minpoly K (ε (1 ⊗ₜ[F] pb.gen) j)).natDegree := minpolyOfDegree K (hint j)
  have hq (j : ι) : poly (q j) ∣ (poly p).map (algebraMap F K) :=
    pb.minpoly_tensorProductPiEquiv_gen_dvd ε j
  let I := {r : Σ d : ℕ, MonicIrreducibleOfDegree K d //
    poly r.2 ∣ (poly p).map (algebraMap F K)}
  let _ : Fintype I := coefficientFactorFintype (algebraMap F K) (poly p) (ne_zero p)
  let _ : ∀ r : I, FiniteDimensional K (AdjoinRoot (poly r.1.2)) :=
    fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
  let c : ι → I := fun j => ⟨⟨_, q j⟩, hq j⟩
  have hc : Function.Bijective c := by
    constructor
    · intro i j hij
      apply pb.minpoly_tensorProductPiEquiv_gen_injective ε
        (Algebra.IsSeparable.isSeparable F pb.gen)
      exact congrArg (fun r : I => poly r.1.2) hij
    · intro r
      have hr : poly r.1.2 ∈ normalizedFactors ((poly p).map (algebraMap F K)) :=
        (Polynomial.mem_normalizedFactors_iff ((monic p).map _).ne_zero).mpr
          ⟨irreducible r.1.2, monic r.1.2, r.2⟩
      obtain ⟨j, hj⟩ :=
        (pb.mem_normalizedFactors_map_minpoly_iff_tensorProductPiEquiv ε (poly r.1.2)).mp hr
      refine ⟨j, Subtype.ext (sigma_poly_injective ?_)⟩
      exact hj
  obtain ⟨g, e, _hg, _he, hcoordinate⟩ :=
    pb.exists_adjoinRoot_equiv_tensorProductPiEquiv_map ε
  -- Keep the native quotient field instances when forming the Milnor maps.
  let g₀ : (F[X] ⧸ Ideal.span {poly p}) ≃ₐ[F] E :=
    { toRingEquiv := g.toRingEquiv
      commutes' := g.commutes }
  let e₀ (j : ι) : (K[X] ⧸ Ideal.span {poly (q j)}) ≃ₐ[K] D j :=
    { toRingEquiv := (e j).toRingEquiv
      commutes' := (e j).commutes }
  let m (j : ι) : (F[X] ⧸ Ideal.span {poly p}) →+*
      (K[X] ⧸ Ideal.span {poly (q j)}) :=
    AdjoinRoot.map (algebraMap F K) (poly p) (poly (q j)) (hq j)
  let jmap (j : ι) : E →+* D j :=
    (Pi.evalRingHom D j).comp
      (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  have hforward (j : ι) : (e₀ j).toRingHom.comp (m j) =
      (jmap j).comp g₀.toRingHom := hcoordinate j
  have hsquare (j : ι) : (e₀ j).symm.toRingHom.comp (jmap j) =
      (m j).comp g₀.symm.toRingHom := by
    apply RingHom.ext
    intro a
    change (e₀ j).symm (jmap j a) = m j (g₀.symm a)
    apply (e₀ j).injective
    calc
      e₀ j ((e₀ j).symm (jmap j a)) = jmap j a := (e₀ j).apply_symm_apply _
      _ = jmap j (g₀ (g₀.symm a)) := by rw [g₀.apply_symm_apply]
      _ = e₀ j (m j (g₀.symm a)) := (RingHom.congr_fun (hforward j) _).symm
  let branch (r : I) : MilnorKRing K :=
    milnorKNormRing K (AdjoinRoot (poly r.1.2))
      (milnorKRingMap
        ((AdjoinRoot.map (algebraMap F K) (poly p) (poly r.1.2) r.2).comp
          g₀.symm.toRingHom) x)
  have hscalar : milnorKRingMap (algebraMap F K) (milnorKNormRing F E x) =
      ∑ r : I, branch r :=
    milnorKNormRing_map_eq_sum_scalarFactors_of_algEquiv (algebraMap F K) p g₀.symm x
  have hbranch (j : ι) : branch (c j) =
      milnorKNormRing K (D j) (milnorKRingMap (jmap j) x) := by
    let _ : FiniteDimensional K (AdjoinRoot (poly (q j))) :=
      (AdjoinRoot.powerBasis' (monic (q j))).finite
    have hleft : branch (c j) = simpleMilnorNorm (q j)
        (milnorKRingMap ((m j).comp g₀.symm.toRingHom) x) :=
      milnorKNormRing_eq_simpleMilnorNorm (q j)
        (milnorKRingMap ((m j).comp g₀.symm.toRingHom) x)
    have hright : milnorKNormRing K (D j) (milnorKRingMap (jmap j) x) =
        simpleMilnorNorm (q j)
          (milnorKRingMap (e₀ j).symm.toRingHom (milnorKRingMap (jmap j) x)) :=
      milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv (q j) (e₀ j).symm
        (milnorKRingMap (jmap j) x)
    have hcomp := milnorKRingMap_comp_apply (jmap j) (e₀ j).symm.toRingHom x
    have hmaps := congrArg
      (fun ψ : E →+* (K[X] ⧸ Ideal.span {poly (q j)}) => milnorKRingMap ψ x)
      (hsquare j)
    have hnorm : simpleMilnorNorm (q j)
        (milnorKRingMap ((m j).comp g₀.symm.toRingHom) x) =
          simpleMilnorNorm (q j)
            (milnorKRingMap (e₀ j).symm.toRingHom (milnorKRingMap (jmap j) x)) :=
      congrArg (simpleMilnorNorm (q j)) (hcomp.trans hmaps).symm
    exact hleft.trans (hnorm.trans hright.symm)
  calc
    milnorKRingMap (algebraMap F K) (milnorKNormRing F E x) =
        ∑ r : I, branch r := hscalar
    _ = ∑ j, branch (c j) := (hc.sum_comp branch).symm
    _ = ∑ j, milnorKNormRing K (D j) (milnorKRingMap (jmap j) x) :=
      Finset.sum_congr rfl fun j _ => hbranch j

/-- The supplied-power-basis tensor formula as equality of the original whole-ring
additive maps, with branch finite-dimensionality proved from their actual coordinates. -/
theorem milnorKNormRing_comp_map_eq_sum_tensorProductPiEquiv_of_powerBasis
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) :
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    (milnorKRingMap (algebraMap F K)).toAddMonoidHom.comp (milnorKNormRing F E) =
      ∑ j, (milnorKNormRing K (D j)).comp
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))).toAddMonoidHom := by
  classical
  intro hFinite
  apply AddMonoidHom.ext
  intro x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.finsetSum_apply]
  exact milnorKNormRing_map_eq_sum_tensorProductPiEquiv_of_powerBasis pb ε x

/-- The supplied-power-basis tensor formula in every original homogeneous group,
including degree zero, with the literal coordinate ring maps. -/
theorem milnorKNorm_map_eq_sum_tensorProductPiEquiv_of_powerBasis
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (n : ℕ) (x : MilnorKTheory E n) :
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKTransport (algebraMap F K) n (milnorKNorm F E n x) =
      ∑ j, milnorKNorm K (D j) n
        (milnorKTransport ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) n x) := by
  intro hFinite
  apply Subtype.ext
  simpa only [milnorKTransport_coe, coe_milnorKNorm,
    AddSubmonoidClass.coe_finsetSum] using
    milnorKNormRing_map_eq_sum_tensorProductPiEquiv_of_powerBasis pb ε (x : MilnorKRing E)

/-- The supplied-power-basis tensor formula as equality of native homogeneous
additive maps in every degree. -/
theorem milnorKNorm_comp_map_eq_sum_tensorProductPiEquiv_of_powerBasis
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (n : ℕ) :
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    (milnorKTransport (algebraMap F K) n).comp (milnorKNorm F E n) =
      ∑ j, (milnorKNorm K (D j) n).comp
        (milnorKTransport ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) n) := by
  classical
  intro hFinite
  apply AddMonoidHom.ext
  intro x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.finsetSum_apply]
  exact milnorKNorm_map_eq_sum_tensorProductPiEquiv_of_powerBasis pb ε n x

/-- For any finite characteristic-zero source extension, the original chosen norm
base-changes to the sum over every factor of the actual full tensor decomposition.
No source presentation or target finiteness witness is supplied by the caller. -/
theorem milnorKNormRing_map_eq_sum_tensorProductPiEquiv
    (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (x : MilnorKRing E) :
    let pb := Field.powerBasisOfFiniteOfSeparable F E
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKRingMap (algebraMap F K) (milnorKNormRing F E x) =
      ∑ j, milnorKNormRing K (D j)
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) x) :=
  milnorKNormRing_map_eq_sum_tensorProductPiEquiv_of_powerBasis
    (Field.powerBasisOfFiniteOfSeparable F E) ε x

/-- The presentation-free full tensor formula as equality of the original
whole-ring additive maps. -/
theorem milnorKNormRing_comp_map_eq_sum_tensorProductPiEquiv
    (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) :
    let pb := Field.powerBasisOfFiniteOfSeparable F E
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    (milnorKRingMap (algebraMap F K)).toAddMonoidHom.comp (milnorKNormRing F E) =
      ∑ j, (milnorKNormRing K (D j)).comp
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))).toAddMonoidHom :=
  milnorKNormRing_comp_map_eq_sum_tensorProductPiEquiv_of_powerBasis
    (Field.powerBasisOfFiniteOfSeparable F E) ε

/-- Presentation-free full tensor base change of the native chosen norm in every
homogeneous degree, including degree zero. -/
theorem milnorKNorm_map_eq_sum_tensorProductPiEquiv
    (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (n : ℕ) (x : MilnorKTheory E n) :
    let pb := Field.powerBasisOfFiniteOfSeparable F E
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKTransport (algebraMap F K) n (milnorKNorm F E n x) =
      ∑ j, milnorKNorm K (D j) n
        (milnorKTransport ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) n x) :=
  milnorKNorm_map_eq_sum_tensorProductPiEquiv_of_powerBasis
    (Field.powerBasisOfFiniteOfSeparable F E) ε n x

/-- Presentation-free full tensor base change as equality of the native
homogeneous additive maps. -/
theorem milnorKNorm_comp_map_eq_sum_tensorProductPiEquiv
    (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (n : ℕ) :
    let pb := Field.powerBasisOfFiniteOfSeparable F E
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    (milnorKTransport (algebraMap F K) n).comp (milnorKNorm F E n) =
      ∑ j, (milnorKNorm K (D j) n).comp
        (milnorKTransport ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) n) :=
  milnorKNorm_comp_map_eq_sum_tensorProductPiEquiv_of_powerBasis
    (Field.powerBasisOfFiniteOfSeparable F E) ε n

end Stacks.Chow

end

/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.RatFunc.CoefficientMap
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Power substitution on the rational function field

Polynomial expansion induces the inclusion sending the lower parameter to a
power of the upper parameter. In positive characteristic the prime-power
calculation supplies pure inseparability and uniqueness of a prime above its
contraction.
-/

@[expose] public noncomputable section

open Polynomial
open scoped nonZeroDivisors

namespace Polynomial

variable (k : Type*) [Field k] (p : ℕ)

/-- The polynomial algebra obtained by substituting the (p)-th power of the parameter. -/
@[instance_reducible]
def frobeniusParameterAlgebra : Algebra k[X] k[X] :=
  (expand k p).toRingHom.toAlgebra

/-- Power substitution of positive degree is finite on the polynomial charts. -/
theorem finite_frobeniusParameterAlgebra (hp : 0 < p) :
    @Module.Finite k[X] k[X] _ _ (frobeniusParameterAlgebra k p).toModule := by
  let := frobeniusParameterAlgebra k p
  let : Module k[X] k[X] := (frobeniusParameterAlgebra k p).toModule
  have hx : IsIntegral k[X] (X : k[X]) := by
    apply IsIntegral.of_pow hp
    rw [← expand_X p]
    exact isIntegral_algebraMap (x := (X : k[X]))
  let S := Algebra.adjoin k[X] ({(X : k[X])} : Set k[X])
  let : Module.Finite k[X] S := Algebra.finite_adjoin_simple_of_isIntegral hx
  apply Module.Finite.of_surjective S.val.toLinearMap
  intro f
  have hX : X ∈ S := Algebra.subset_adjoin (Set.mem_singleton _)
  have hC (c : k) : C c ∈ S := by
    rw [← expand_C p c]
    exact S.algebraMap_mem (C c)
  have hf : f ∈ S := by
    induction f using Polynomial.induction_on' with
    | add f g hf hg => exact S.add_mem hf hg
    | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial]
      exact S.mul_mem (hC c) (S.pow_mem hX n)
  exact ⟨⟨f, hf⟩, rfl⟩

/-- The (p)-th power is in the image of parameter substitution in characteristic (p). -/
theorem expand_map_frobenius [ExpChar k p] (f : k[X]) :
    expand k p (f.map (frobenius k p)) = f ^ p := by
  rw [← map_expand, map_frobenius_expand]

/-- An upper prime is determined by its contraction under parameter substitution. -/
theorem eq_of_comap_expand_eq [ExpChar k p] (hp : 0 < p)
    {P Q : Ideal k[X]} [P.IsPrime] [Q.IsPrime]
    (h : P.comap (expand k p).toRingHom = Q.comap (expand k p).toRingHom) : P = Q := by
  ext f
  rw [← (inferInstance : P.IsPrime).pow_mem_iff_mem p hp,
    ← (inferInstance : Q.IsPrime).pow_mem_iff_mem p hp, ← expand_map_frobenius k p f]
  change f.map (frobenius k p) ∈ P.comap (expand k p).toRingHom ↔
    f.map (frobenius k p) ∈ Q.comap (expand k p).toRingHom
  rw [h]

end Polynomial

namespace RatFunc

variable (k : Type*) [Field k] (p : ℕ) (hp : 0 < p)

/-- The native rational function map given by substituting the (p)-th power of the parameter. -/
def frobeniusParameter : RatFunc k →ₐ[k] RatFunc k :=
  RatFunc.mapAlgHom (expand k p)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
      (expand k p).toRingHom (expand_injective (R := k) hp))

@[simp]
theorem frobeniusParameter_algebraMap (f : k[X]) :
    frobeniusParameter k p hp (algebraMap k[X] (RatFunc k) f) =
      algebraMap k[X] (RatFunc k) (expand k p f) := by
  exact RatFunc.mapRingHom_algebraMap (expand k p).toRingHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
      (expand k p).toRingHom (expand_injective (R := k) hp)) f

@[simp]
theorem frobeniusParameter_C (c : k) :
    frobeniusParameter k p hp (RatFunc.C c) = RatFunc.C c :=
  (frobeniusParameter k p hp).commutes c

@[simp]
theorem frobeniusParameter_X :
    frobeniusParameter k p hp (X : RatFunc k) = (X : RatFunc k) ^ p := by
  rw [← RatFunc.algebraMap_X, frobeniusParameter_algebraMap, expand_X, map_pow]

/-- The algebra for the inclusion of rational function fields by power substitution. -/
@[instance_reducible]
def frobeniusParameterAlgebra : Algebra (RatFunc k) (RatFunc k) :=
  (frobeniusParameter k p hp).toRingHom.toAlgebra

/-- The degree of power substitution is the exponent. -/
theorem finrank_frobeniusParameterAlgebra :
    @Module.finrank (RatFunc k) (RatFunc k) _ _
      (frobeniusParameterAlgebra k p hp).toModule = p := by
  let f := (X : RatFunc k) ^ p
  let L := IntermediateField.adjoin k {f}
  let e : RatFunc k ≃ₐ[k] L := algEquivOfTranscendental f (transcendental_X.pow hp)
  have he : L.val.comp e.toAlgHom = frobeniusParameter k p hp := by
    let j := IsScalarTower.toAlgHom k k[X] (RatFunc k)
    have h : (L.val.comp e.toAlgHom).comp j = (frobeniusParameter k p hp).comp j := by
      apply Polynomial.algHom_ext
      change ((e (algebraMap k[X] (RatFunc k) (Polynomial.X : k[X])) : L) : RatFunc k) =
        frobeniusParameter k p hp (algebraMap k[X] (RatFunc k) (Polynomial.X : k[X]))
      rw [RatFunc.algebraMap_X, frobeniusParameter_X]
      exact algEquivOfTranscendental_X f (transcendental_X.pow hp)
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
    exact congrArg AlgHom.toRingHom h
  have hcomm : (algebraMap L (RatFunc k)).comp e.toRingEquiv.toRingHom =
      (RingEquiv.refl (RatFunc k)).toRingHom.comp (frobeniusParameter k p hp).toRingHom := by
    apply RingHom.ext
    intro x
    change (e x : RatFunc k) = frobeniusParameter k p hp x
    exact DFunLike.congr_fun he x
  have hf : f = algebraMap k[X] (RatFunc k) ((Polynomial.X : k[X]) ^ p) := by
    rw [map_pow, RatFunc.algebraMap_X]
  calc
    _ = Module.finrank L (RatFunc k) :=
      @Algebra.finrank_eq_of_equiv_equiv (RatFunc k) (RatFunc k) _ _
        (frobeniusParameterAlgebra k p hp) L (RatFunc k) _ _ _
        e.toRingEquiv (RingEquiv.refl (RatFunc k)) hcomm
    _ = max f.num.natDegree f.denom.natDegree := finrank_eq_max_natDegree f
    _ = p := by
      rw [hf, num_algebraMap, denom_algebraMap, natDegree_X_pow, natDegree_one]
      exact max_eq_left (Nat.zero_le p)

/-- The rational extension given by power substitution is finite. -/
theorem finite_frobeniusParameterAlgebra :
    @FiniteDimensional (RatFunc k) (RatFunc k) _ _
      (frobeniusParameterAlgebra k p hp).toModule := by
  let : Module (RatFunc k) (RatFunc k) := (frobeniusParameterAlgebra k p hp).toModule
  exact FiniteDimensional.of_finrank_pos ((finrank_frobeniusParameterAlgebra k p hp).symm ▸ hp)

/-- Parameter substitution by the characteristic gives a purely inseparable extension. -/
theorem isPurelyInseparable_frobeniusParameterAlgebra [ExpChar k p] :
    letI := frobeniusParameterAlgebra k p hp
    IsPurelyInseparable (RatFunc k) (RatFunc k) := by
  let := frobeniusParameterAlgebra k p hp
  let : ExpChar (RatFunc k) p :=
    expChar_of_injective_algebraMap (algebraMap k (RatFunc k)).injective p
  apply (isPurelyInseparable_iff_pow_mem (RatFunc k) p).mpr
  intro x
  refine ⟨1, algebraMap k[X] (RatFunc k) (x.num.map (frobenius k p)) /
    algebraMap k[X] (RatFunc k) (x.denom.map (frobenius k p)), ?_⟩
  change frobeniusParameter k p hp _ = _
  rw [map_div₀, frobeniusParameter_algebraMap, frobeniusParameter_algebraMap,
    expand_map_frobenius, expand_map_frobenius, map_pow, map_pow, ← div_pow,
    num_div_denom, pow_one]

end RatFunc

end

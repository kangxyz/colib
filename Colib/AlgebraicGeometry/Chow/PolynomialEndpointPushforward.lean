/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointFiber
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension

/-!
# Finite pushforward of polynomial endpoint cycles

The coefficient at an actual target endpoint point is the sum of the full
source endpoint coefficients over it with their actual residue-field degrees.
The finite principal-divisor norm identity computes this sum as the generic
function-field degree times the full target endpoint coefficient.

This supplies the native cycle identity used by Motivic at
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/Diagonal/NormalizedEndpointCycles.lean:63-82`, and is
the ambient-cycle version of the finite-curve identity in
`FiniteCurvePushforwardSpecialization.lean:459-467` under
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Endpoints`.
It uses `Stacks.Chow.finsum_ord_mul_residueDegree_of_isFinite` and the order
of a power from the Stacks pin `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Polynomial

universe u

namespace Stacks.Chow.PolynomialEndpointFiber

variable {k : Type u} [Field k] {P Q : Scheme.{u}}

private theorem coheight_eq_one_of_finitePolynomialFamily [IsIntegral P]
    (f : P ⟶ Spec (.of k[X])) [IsFinite f] (x : P) (hx : x ≠ genericPoint P) :
    Order.coheight x = 1 := by
  have hdim : (Order.coheight x : WithBot ℕ∞) ≤ 1 := calc
    _ ≤ Order.krullDim P := Order.coheight_le_krullDim x
    _ = topologicalKrullDim P := by
      rw [topologicalKrullDim]
      exact Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := P)).symm
    _ ≤ topologicalKrullDim (Spec (.of k[X])) := topologicalKrullDim_le_of_isIntegralHom f
    _ = 1 := by
      change topologicalKrullDim (PrimeSpectrum k[X]) = 1
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
        Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      rfl
  have hlt : x < (⊤ : P) := by
    refine lt_iff_le_not_ge.mpr ⟨le_top, ?_⟩
    intro h
    have hs : x ⤳ genericPoint P := h
    exact hx (Specializes.antisymm hs (genericPoint_specializes x)).eq
  refine le_antisymm ?_ (Order.one_le_iff_ne_zero.mpr (ne_of_gt (Order.coheight_pos_of_lt_top hlt)))
  exact_mod_cast hdim

private theorem endpoint_ne_genericPoint (a : k) (x : Spec (.of k)) :
    endpoint a x ≠ genericPoint (Spec (.of k[X])) := by
  intro hx
  have hm : Polynomial.X - Polynomial.C a ∈ (endpoint a x).asIdeal := by
    change Polynomial.evalRingHom a (Polynomial.X - Polynomial.C a) ∈ x.asIdeal
    simp
  rw [hx, genericPoint_eq_bot_of_affine] at hm
  exact Polynomial.X_sub_C_ne_zero a (Ideal.mem_bot.mp hm)

private theorem fiberInclusion_ne_genericPoint [IsIntegral P]
    (f : P ⟶ Spec (.of k[X])) [Flat f] (a : k) (y : fiber f a) :
    fiberInclusion f a y ≠ genericPoint P := by
  intro hy
  have hη : genericPoint P ∈ genericPoints P := by simp [genericPoints_eq_singleton]
  have hg : f (genericPoint P) = genericPoint (Spec (.of k[X])) := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using
      mem_genericPoints_of_flat f hη
  have hc : endpoint a (pullback.fst (endpoint a) f y) = f (fiberInclusion f a y) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun m : fiber f a ⟶ Spec (.of k[X]) => m y)
        (pullback.condition (f := endpoint a) (g := f))
  exact endpoint_ne_genericPoint a _ (hc.trans ((congrArg (fun x : P => f x) hy).trans hg))

private theorem range_fiberInclusion_comp_subset
    (f : P ⟶ Spec (.of k[X])) (g : Q ⟶ Spec (.of k[X]))
    (p : P ⟶ Q) (hp : p ≫ g = f) (a : k) :
    Set.range (fiberInclusion f a ≫ p) ⊆ Set.range (fiberInclusion g a) := by
  rintro _ ⟨x, rfl⟩
  let v : fiber f a ⟶ fiber g a :=
    pullback.lift (pullback.fst (endpoint a) f) (fiberInclusion f a ≫ p) (by
      rw [Category.assoc, hp]
      exact pullback.condition)
  have hv : v ≫ fiberInclusion g a = fiberInclusion f a ≫ p := pullback.lift_snd _ _ _
  exact ⟨v x, by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : fiber f a ⟶ Q => m x) hv⟩

variable [IsIntegral P] [IsIntegral Q]

private theorem rationalFunction_comp (p : P ⟶ Q) [IsDominant p]
    (g : Q ⟶ Spec (.of k[X])) (a : k) :
    rationalFunction (p ≫ g) a = dominantFunctionFieldMap p (rationalFunction g a) := by
  let : Nonempty ((⊤ : P.Opens) : Type u) := ⟨⟨genericPoint P, trivial⟩⟩
  let : Nonempty ((⊤ : Q.Opens) : Type u) := ⟨⟨genericPoint Q, trivial⟩⟩
  have h := DFunLike.congr_fun (appLE_germToFunctionField_commutes p ⊤ ⊤ le_top) (equation g a)
  have happ : p.appLE ⊤ ⊤ le_top = p.appTop := Scheme.Hom.appLE_eq_app p (U := ⊤)
  rw [happ] at h
  have heq : equation (p ≫ g) a = p.appTop (equation g a) := by
    simp only [equation, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  change P.germToFunctionField ⊤ (equation (p ≫ g) a) =
    dominantFunctionFieldMap p (Q.germToFunctionField ⊤ (equation g a))
  rw [heq]
  exact h

variable (f : P ⟶ Spec (.of k[X])) [IsFinite f] [Flat f]
  (g : Q ⟶ Spec (.of k[X])) [IsFinite g] [Flat g] (p : P ⟶ Q) [IsFinite p] [IsDominant p]

/-- The coefficient at a target endpoint counts each branch with its length and degree. -/
theorem finiteCyclePushforward_fundamentalCycle_comp_apply
    (hp : p ≫ g = f) (a : k) (y : fiber g a) :
    letI : Algebra Q.functionField P.functionField := (dominantFunctionFieldMap p).toAlgebra
    letI : IsNoetherian (fiber f a) := fiber_isNoetherian f a
    letI : IsNoetherian (fiber g a) := fiber_isNoetherian g a
    finiteCyclePushforward (fiberInclusion f a ≫ p) (AlgebraicCycle.fundamentalCycle (fiber f a))
        (fiberInclusion g a y) =
      (Module.finrank Q.functionField P.functionField : ℤ) *
        finiteCyclePushforward (fiberInclusion g a) (AlgebraicCycle.fundamentalCycle (fiber g a))
          (fiberInclusion g a y) := by
  classical
  let : Algebra Q.functionField P.functionField := (dominantFunctionFieldMap p).toAlgebra
  let : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian g
  let : IsNoetherian (fiber f a) := fiber_isNoetherian f a
  let : IsNoetherian (fiber g a) := fiber_isNoetherian g a
  have hy := fiberInclusion_ne_genericPoint g a y
  have hcoQ := coheight_eq_one_of_finitePolynomialFamily g (fiberInclusion g a y) hy
  have hηp : p (genericPoint P) = genericPoint Q :=
    ((tfae_isDominant_of_isIntegral p).out 1 2).mp (inferInstance : IsDominant p)
  have hcoP (x : P) (hx : p.base x = fiberInclusion g a y) : Order.coheight x = 1 := by
    apply coheight_eq_one_of_finitePolynomialFamily f x
    intro hxη
    exact hy (hx.symm.trans ((congrArg (fun z : P => p z) hxη).trans hηp))
  have halg : algebraMap Q.functionField P.functionField = dominantFunctionFieldMap p :=
    RingHom.algebraMap_toAlgebra _
  have hrat : rationalFunction f a =
      algebraMap Q.functionField P.functionField (rationalFunction g a) := by
    rw [← hp, halg]
    exact rationalFunction_comp p g a
  have hcoeff (x : P) (hx : x ∈ p.base ⁻¹' {fiberInclusion g a y}) :
      finiteCyclePushforward (fiberInclusion f a) (AlgebraicCycle.fundamentalCycle (fiber f a)) x *
          (p.residueDegree x : ℤ) = P.ord (rationalFunction f a) x * (p.residueDegree x : ℤ) := by
    have hxy : p.base x = fiberInclusion g a y := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx
    rw [finiteCyclePushforward_fundamentalCycle_apply_eq_ord f a x (hcoP x hxy)]
  rw [← finiteCyclePushforward_comp_apply (fiberInclusion f a) p, finiteCyclePushforward_apply p,
    finsum_mem_congr rfl hcoeff, finsum_ord_mul_residueDegree_of_isFinite p halg
      (rationalFunction f a) (rationalFunction_ne_zero f a) _ hcoQ hcoP,
    hrat, Algebra.norm_algebraMap, Scheme.ord_pow (rationalFunction_ne_zero g a),
    finiteCyclePushforward_fundamentalCycle_apply_eq_ord g a _ hcoQ]

/-- The full pushed endpoint fundamental cycle scales by the actual function-field degree. -/
theorem finiteCyclePushforward_fundamentalCycle_comp (hp : p ≫ g = f) (a : k) :
    letI : Algebra Q.functionField P.functionField := (dominantFunctionFieldMap p).toAlgebra
    letI : IsNoetherian (fiber f a) := fiber_isNoetherian f a
    letI : IsNoetherian (fiber g a) := fiber_isNoetherian g a
    finiteCyclePushforward (fiberInclusion f a ≫ p) (AlgebraicCycle.fundamentalCycle (fiber f a)) =
      (Module.finrank Q.functionField P.functionField : ℤ) •
        finiteCyclePushforward (fiberInclusion g a)
          (AlgebraicCycle.fundamentalCycle (fiber g a)) := by
  classical
  let : Algebra Q.functionField P.functionField := (dominantFunctionFieldMap p).toAlgebra
  let : IsNoetherian (fiber f a) := fiber_isNoetherian f a
  let : IsNoetherian (fiber g a) := fiber_isNoetherian g a
  apply Function.locallyFinsuppWithin.ext
  intro y
  simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, zsmul_eq_mul]
  by_cases hy : y ∈ Set.range (fiberInclusion g a)
  · obtain ⟨z, rfl⟩ := hy
    exact finiteCyclePushforward_fundamentalCycle_comp_apply f g p hp a z
  · have hx : y ∉ Set.range (fiberInclusion f a ≫ p) := fun h =>
      hy (range_fiberInclusion_comp_subset f g p hp a h)
    rw [finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range
        (fiberInclusion f a ≫ p) y hx,
      finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range (fiberInclusion g a) y hy,
      mul_zero]

end Stacks.Chow.PolynomialEndpointFiber

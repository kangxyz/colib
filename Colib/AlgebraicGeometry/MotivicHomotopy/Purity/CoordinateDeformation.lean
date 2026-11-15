/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.DeformationLaurent

/-!
# Polynomial presentation of coordinate deformation charts

Scaling the normal variables by the Laurent variable and sending the
deformation parameter to its inverse gives the polynomial presentation
of the extended Rees algebra of the coordinate ideal.
-/

@[expose] public noncomputable section

open AlgebraicGeometry LaurentPolynomial TopologicalSpace

namespace Stacks.Deformation

section Laurent

variable {R σ : Type*} [CommRing R]

/-- Laurent evaluation of coefficients with each normal variable scaled by `T 1`. -/
def coordinateDeformationLaurentCoeff :
    MvPolynomial σ R →+* LaurentPolynomial (MvPolynomial σ R) :=
  MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp MvPolynomial.C)
    (fun j => LaurentPolynomial.C (MvPolynomial.X j) * T 1)

/-- The Laurent presentation sends each normal variable to the original
variable times `T 1` and the deformation parameter to `T (-1)`. -/
def coordinateDeformationLaurentHom :
    Polynomial (MvPolynomial σ R) →+* LaurentPolynomial (MvPolynomial σ R) :=
  Polynomial.eval₂RingHom coordinateDeformationLaurentCoeff (T (-1))

private theorem coordinateDeformationLaurentCoeff_monomial (β : σ →₀ ℕ) (r : R) :
    coordinateDeformationLaurentCoeff (MvPolynomial.monomial β r) =
      LaurentPolynomial.C (MvPolynomial.monomial β r) * T (Finsupp.degree β : ℕ) := by
  have hT :
      (∏ i ∈ β.support, (T 1 : LaurentPolynomial (MvPolynomial σ R)) ^ β i) =
        T (Finsupp.degree β : ℕ) := by
    rw [Finset.prod_pow_eq_pow_sum, T_pow, mul_one, Finsupp.degree_apply]
  rw [coordinateDeformationLaurentCoeff, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply,
    MvPolynomial.monomial_eq, map_mul]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, hT, mul_assoc]

/-- A normal monomial of degree `β.degree` times the `d`th power of the
parameter occurs in Laurent degree `β.degree - d`. -/
theorem coordinateDeformationLaurentHom_monomial (β : σ →₀ ℕ) (d : ℕ) (r : R) :
    coordinateDeformationLaurentHom (Polynomial.monomial d (MvPolynomial.monomial β r)) =
      LaurentPolynomial.C (MvPolynomial.monomial β r) * T ((↑β.degree : ℤ) - d) := by
  simp only [coordinateDeformationLaurentHom, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_monomial, coordinateDeformationLaurentCoeff_monomial, T_pow, mul_neg_one,
    mul_T_assoc, sub_eq_add_neg]

private theorem coordinateDeformationLaurentHom_coeff (p : Polynomial (MvPolynomial σ R))
    (n : ℤ) (β : σ →₀ ℕ) :
    ((coordinateDeformationLaurentHom p).coeff n).coeff β =
      if n ≤ (↑β.degree : ℤ) then (p.coeff ((↑β.degree : ℤ) - n).toNat).coeff β else 0 := by
  classical
  let P (p : Polynomial (MvPolynomial σ R)) : Prop :=
    ((coordinateDeformationLaurentHom p).coeff n).coeff β =
      if n ≤ (↑β.degree : ℤ) then (p.coeff ((↑β.degree : ℤ) - n).toNat).coeff β else 0
  change P p
  have hAdd (p q : Polynomial (MvPolynomial σ R)) (hp : P p) (hq : P q) : P (p + q) := by
    dsimp only [P] at hp hq ⊢
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.coeff_add]
      at hp hq ⊢
    rw [hp, hq]
    split <;> simp
  refine Polynomial.induction_on' p hAdd ?_
  intro d a
  refine MvPolynomial.induction_on' a ?_ ?_
  · intro γ r
    dsimp only [P]
    rw [coordinateDeformationLaurentHom_monomial, ← single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Polynomial.coeff_monomial]
    by_cases hγ : γ = β
    · subst γ
      by_cases hn : n ≤ (↑β.degree : ℤ)
      · have he : ((↑β.degree : ℤ) - d = n) ↔
            d = ((↑β.degree : ℤ) - n).toNat := by omega
        simp only [ite_eq_left hn, he]
      · have he : (↑β.degree : ℤ) - d ≠ n := by omega
        simp [hn, he]
    · split_ifs <;> simp [hγ]
  · intro a b ha hb
    rw [map_add]
    exact hAdd _ _ ha hb

/-- Laurent coefficients recover every coefficient of the source polynomial. -/
theorem coordinateDeformationLaurentHom_injective :
    Function.Injective (coordinateDeformationLaurentHom (σ := σ) (R := R)) := by
  intro p q hpq
  apply Polynomial.ext
  intro d
  apply MvPolynomial.ext
  intro β
  let n : ℤ := (↑β.degree : ℤ) - d
  have hn : n ≤ (↑β.degree : ℤ) := by dsimp [n]; omega
  have hd : ((↑β.degree : ℤ) - n).toNat = d := by dsimp [n]; omega
  have h := congrArg (fun L : LaurentPolynomial (MvPolynomial σ R) => (L.coeff n).coeff β) hpq
  simpa only [coordinateDeformationLaurentHom_coeff, ite_eq_left hn, hd] using h

private def coordinateDeformationLaurentPreimage (n : ℤ) (a : MvPolynomial σ R) :
    Polynomial (MvPolynomial σ R) :=
  ∑ β ∈ a.support, Polynomial.monomial ((↑β.degree : ℤ) - n).toNat
    (MvPolynomial.monomial β (a.coeff β))

private theorem coordinateDeformationLaurentHom_preimage
    (n : ℤ) (a : MvPolynomial σ R) (ha : a ∈ MvPolynomial.idealOfVars σ R ^ n.toNat) :
    coordinateDeformationLaurentHom (coordinateDeformationLaurentPreimage n a) =
      LaurentPolynomial.C a * T n := by
  classical
  have h (β : σ →₀ ℕ) (hβ : β ∈ a.support) :
      (↑β.degree : ℤ) - ((↑β.degree : ℤ) - n).toNat = n := by
    have := (MvPolynomial.mem_pow_idealOfVars_iff _ _).1 ha β hβ
    omega
  rw [coordinateDeformationLaurentPreimage, map_sum]
  calc
    _ = ∑ β ∈ a.support, LaurentPolynomial.C (MvPolynomial.monomial β (a.coeff β)) * T n := by
      apply Finset.sum_congr rfl
      intro β hβ
      rw [coordinateDeformationLaurentHom_monomial, h β hβ]
    _ = LaurentPolynomial.C a * T n := by
      rw [← Finset.sum_mul, ← map_sum, MvPolynomial.support_sum_monomial_coeff]

/-- The image consists of Laurent polynomials whose coefficient in degree `n`
belongs to the `n.toNat`th power of the coordinate ideal. -/
theorem mem_range_coordinateDeformationLaurentHom_iff
    (L : LaurentPolynomial (MvPolynomial σ R)) :
    L ∈ Set.range coordinateDeformationLaurentHom ↔
      ∀ n, L.coeff n ∈ MvPolynomial.idealOfVars σ R ^ n.toNat := by
  constructor
  · rintro ⟨p, rfl⟩ n
    apply (MvPolynomial.mem_pow_idealOfVars_iff' _ _).2
    intro β hβ
    rw [coordinateDeformationLaurentHom_coeff, ite_eq_right (by omega)]
  · intro h
    classical
    have hL :
        ∑ n ∈ L.coeff.support, LaurentPolynomial.C (L.coeff n) * T n = L := by
      simp_rw [← single_eq_C_mul_T]
      apply AddMonoidAlgebra.ext
      rw [AddMonoidAlgebra.coeff_sum]
      exact Finsupp.sum_single L.coeff
    refine ⟨∑ n ∈ L.coeff.support, coordinateDeformationLaurentPreimage n (L.coeff n), ?_⟩
    simpa only [map_sum, coordinateDeformationLaurentHom_preimage _ _ (h _)] using hL

end Laurent

section Chart

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData) (W : X.affineOpens)
  {R σ : Type*} [CommRing R] (θ : Γ(X, W.1) ≃+* MvPolynomial σ R)
  (hθ : Ideal.map θ.toRingHom (I.ideal W) = MvPolynomial.idealOfVars σ R)

include hθ in
private theorem coordinateDeformationChartVar_mem (j : σ) :
    θ.symm (MvPolynomial.X j) ∈ I.ideal W := by
  apply Ideal.symm_apply_mem_of_equiv_iff.2
  change MvPolynomial.X j ∈ Ideal.map θ.toRingHom (I.ideal W)
  rw [hθ]
  exact Ideal.subset_span ⟨j, rfl⟩

/-- The normal coordinate is the original homogeneous section of degree one
associated to the corresponding generator of the coordinate ideal. -/
def coordinateDeformationChartVar (j : σ) :
    Γ(deformationSpace I, deformationSpaceToBase I ⁻¹ᵁ W.1) :=
  chartIncl I 1 W.1 (extReesOfMem I W 1 (θ.symm (MvPolynomial.X j))
    (by simpa only [pow_one] using coordinateDeformationChartVar_mem I W θ hθ j))

/-- Polynomial evaluation on the actual extended-Rees chart, with its original
normal coordinates and deformation parameter. -/
def coordinateDeformationChartHom :
    Polynomial (MvPolynomial σ R) →+*
      Γ(deformationSpace I, deformationSpaceToBase I ⁻¹ᵁ W.1) :=
  Polynomial.eval₂RingHom
    (MvPolynomial.eval₂Hom
      (((deformationSpaceToBase I).app W.1).hom.comp (θ.symm.toRingHom.comp MvPolynomial.C))
      (coordinateDeformationChartVar I W θ hθ))
    (paramChartOf I W.1)

private def coordinateDeformationChartLaurentHom :
    Γ(deformationSpace I, deformationSpaceToBase I ⁻¹ᵁ W.1) →+*
      LaurentPolynomial (MvPolynomial σ R) :=
  (AddMonoidAlgebra.mapRingHom ℤ θ.toRingHom).comp (chartLaurent I W)

private theorem coordinateDeformationChartLaurentHom_injective :
    Function.Injective (coordinateDeformationChartLaurentHom I W θ) :=
  (AddMonoidAlgebra.mapRingEquiv ℤ θ).injective.comp <|
    (extReesLaurent_injective I W.1).comp
      (RingEquiv.ofBijective (chartRingHom I W.1) (bijective_chartRingHom I W)).symm.injective

private theorem coordinateDeformationChartLaurentHom_chartIncl (n : ℤ)
    (x : ((extReesGradedAlgebra I).piece n).val.obj (Opposite.op W.1)) :
    coordinateDeformationChartLaurentHom I W θ (chartIncl I n W.1 x) =
      LaurentPolynomial.C (θ (extReesAmbient I n W.1 x)) * T n := by
  rw [coordinateDeformationChartLaurentHom, RingHom.comp_apply, ← chartRingHom_incl,
    chartLaurent_chartRingHom, extReesLaurent_incl, ← single_eq_C_mul_T,
    AddMonoidAlgebra.mapRingHom_single, single_eq_C_mul_T]
  rfl

private theorem coordinateDeformationChartLaurentHom_comp :
    (coordinateDeformationChartLaurentHom I W θ).comp (coordinateDeformationChartHom I W θ hθ) =
      coordinateDeformationLaurentHom := by
  apply Polynomial.ringHom_ext'
  · rw [RingHom.comp_assoc]
    simp only [coordinateDeformationChartHom, coordinateDeformationLaurentHom,
      Polynomial.eval₂RingHom_comp_C]
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, coordinateDeformationLaurentCoeff,
        coordinateDeformationChartLaurentHom, chartLaurent_app, ← single_eq_C,
        AddMonoidAlgebra.mapRingHom_single, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply]
    · intro j
      rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', coordinateDeformationLaurentCoeff,
        MvPolynomial.eval₂Hom_X', coordinateDeformationChartVar,
        coordinateDeformationChartLaurentHom_chartIncl]
      have h := extReesAmbient_extReesOfMem I W 1 (θ.symm (MvPolynomial.X j))
        (by simpa only [pow_one] using coordinateDeformationChartVar_mem I W θ hθ j)
      exact congrArg (fun a => LaurentPolynomial.C a * T 1)
        ((congrArg (fun a => θ a) h).trans (θ.apply_symm_apply _))
  · simp only [RingHom.comp_apply, coordinateDeformationChartHom, coordinateDeformationLaurentHom,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, coordinateDeformationChartLaurentHom,
      chartLaurent_paramChartOf, T, AddMonoidAlgebra.mapRingHom_single, map_one]

private theorem coordinateDeformationChartHom_bijective :
    Function.Bijective (coordinateDeformationChartHom I W θ hθ) := by
  constructor
  · intro p q hpq
    apply coordinateDeformationLaurentHom_injective
    rw [← coordinateDeformationChartLaurentHom_comp I W θ hθ]
    exact congrArg (coordinateDeformationChartLaurentHom I W θ) hpq
  · intro y
    induction y using chartIncl_induction I W with
    | h0 => exact ⟨0, map_zero _⟩
    | hadd a b ha hb =>
      obtain ⟨p, rfl⟩ := ha
      obtain ⟨q, rfl⟩ := hb
      exact ⟨p + q, map_add _ p q⟩
    | hincl n x =>
      have h : extReesAmbient I n W.1 x ∈ I.ideal W ^ n.toNat := by
        simpa only [Int.toNat_natCast] using
          Stacks.Blowup.reesPieceAmbient_mem_affine I (n.toNat : ℤ) (Int.natCast_nonneg _) W x
      have h' := Ideal.mem_map_of_mem θ.toRingHom h
      rw [Ideal.map_pow, hθ] at h'
      refine ⟨coordinateDeformationLaurentPreimage n (θ (extReesAmbient I n W.1 x)),
        coordinateDeformationChartLaurentHom_injective I W θ ?_⟩
      rw [coordinateDeformationChartLaurentHom_chartIncl, ← RingHom.comp_apply,
        coordinateDeformationChartLaurentHom_comp I W θ hθ]
      exact coordinateDeformationLaurentHom_preimage n _ h'

/-- The actual coordinate deformation chart is polynomial in the normal
coordinates and the original deformation parameter. -/
def coordinateDeformationChartEquiv :
    Polynomial (MvPolynomial σ R) ≃+*
      Γ(deformationSpace I, deformationSpaceToBase I ⁻¹ᵁ W.1) :=
  RingEquiv.ofBijective (coordinateDeformationChartHom I W θ hθ)
    (by exact coordinateDeformationChartHom_bijective I W θ hθ)

/-- The polynomial variable is the original deformation parameter. -/
@[simp]
theorem coordinateDeformationChartEquiv_X :
    coordinateDeformationChartEquiv I W θ hθ Polynomial.X = paramChartOf I W.1 :=
  Polynomial.eval₂_X _ _

/-- The normal variable is the original degree-one coordinate section. -/
@[simp]
theorem coordinateDeformationChartEquiv_C_X (j : σ) :
    coordinateDeformationChartEquiv I W θ hθ (Polynomial.C (MvPolynomial.X j)) =
      coordinateDeformationChartVar I W θ hθ j := by
  simp [coordinateDeformationChartEquiv, coordinateDeformationChartHom]

/-- The coefficient map is the pullback of the corresponding function on the base. -/
@[simp]
theorem coordinateDeformationChartEquiv_C_C (r : R) :
    coordinateDeformationChartEquiv I W θ hθ (Polynomial.C (MvPolynomial.C r)) =
      ((deformationSpaceToBase I).app W.1).hom (θ.symm (MvPolynomial.C r)) := by
  simp [coordinateDeformationChartEquiv, coordinateDeformationChartHom]

/-- The pullback of an original coordinate is the parameter times the normal coordinate. -/
theorem coordinateDeformationChartEquiv_param_mul_C_X (j : σ) :
    paramChartOf I W.1 * coordinateDeformationChartEquiv I W θ hθ
        (Polynomial.C (MvPolynomial.X j)) =
      ((deformationSpaceToBase I).app W.1).hom (θ.symm (MvPolynomial.X j)) := by
  rw [coordinateDeformationChartEquiv_C_X, coordinateDeformationChartVar]
  exact (deformationSpaceToBase_app_eq_param_mul I W _
    (coordinateDeformationChartVar_mem I W θ hθ j)).symm

end Chart

end Stacks.Deformation

end

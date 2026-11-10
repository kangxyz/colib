/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactor
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Original scalar factors lift through the actual relative presentation

For an actual embedding of two original root fields, every scalar factor of the
top polynomial selects a unique scalar factor of the lower polynomial. The lower
quotient embeds in the original top factor quotient, with the original field-map
square. Its polynomial is characterized by the kernel of literal evaluation at
the image of the original lower root.

The original relative polynomial `towerFactor` then has an actual scalar factor
over this lower quotient. That factor's literal quotient is ring equivalent to
the original top factor quotient. The equivalence retains the lower coefficient
map, relative coefficient-factor map, and original top root.

This is the forward direction of nested scalar-factor grouping. It does not yet
provide a bijection on the complete dependent pair index, its inverse direction,
or any norm, multiplicity, separability, or induction theorem. All carriers are
native polynomial quotients and native monic-irreducible factor indices.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

private theorem nestedScalarFactors_sigma_poly_injective {K : Type*} [Field K] :
    Function.Injective (fun r : Σ d : ℕ, MonicIrreducibleOfDegree K d => poly r.2) := by
  intro r s h
  obtain ⟨d, r⟩ := r
  obtain ⟨e, s⟩ := s
  change poly r = poly s at h
  obtain rfl : d = e := by rw [← natDegree_eq r, h, natDegree_eq s]
  obtain rfl := poly_injective h
  rfl

local instance {K : Type*} [Field K] {d : ℕ} (r : MonicIrreducibleOfDegree K d) :
    Fact (Irreducible (poly r)) := ⟨irreducible r⟩

/-- A root in an actual field quotient selects a unique native factor and an
actual coefficient-preserving embedding of its quotient. -/
theorem existsUnique_factor_algHom_of_root {K L : Type*} [Field K] [Field L]
    [Algebra K L] (P : K[X]) (hP : P ≠ 0) (x : L) (hx : aeval x P = 0) :
    ∃! r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ P},
      ∃ i : AdjoinRoot (poly r.1.2) →ₐ[K] L, i (root (poly r.1.2)) = x := by
  have hint : IsIntegral K x := (show IsAlgebraic K x from ⟨P, hP, hx⟩).isIntegral
  let r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ P} :=
    ⟨⟨(minpoly K x).natDegree,
      ⟨minpoly K x, minpoly.monic hint, minpoly.irreducible hint, rfl⟩⟩,
      minpoly.dvd K x hx⟩
  let i : AdjoinRoot (poly r.1.2) →ₐ[K] L :=
    liftAlgHom (poly r.1.2) (Algebra.ofId K L) x (minpoly.aeval K x)
  refine ⟨r, ⟨i, liftAlgHom_root _ _ _ _⟩, ?_⟩
  rintro s ⟨j, hj⟩
  apply Subtype.ext
  apply nestedScalarFactors_sigma_poly_injective
  change poly s.1.2 = minpoly K x
  apply minpoly.eq_of_irreducible_of_monic (irreducible s.1.2) _ (monic s.1.2)
  rw [← hj]
  exact aeval_algHom_eq_zero (poly s.1.2) j

/-- The selected lower factor is the literal kernel of evaluation. In particular,
this identifies its actual prime ideal, not only the factor degree. -/
theorem factor_span_eq_ker_eval₂_of_algHom {K L : Type*} [Field K] [Field L]
    [Algebra K L] {d : ℕ} (r : MonicIrreducibleOfDegree K d)
    (i : AdjoinRoot (poly r) →ₐ[K] L) :
    Ideal.span {poly r} =
      RingHom.ker (Polynomial.eval₂RingHom (algebraMap K L) (i (root (poly r)))) := by
  have hr : poly r = minpoly K (i (root (poly r))) :=
    minpoly.eq_of_irreducible_of_monic (irreducible r)
      (aeval_algHom_eq_zero (poly r) i) (monic r)
  ext a
  rw [Ideal.mem_span_singleton, RingHom.mem_ker]
  change poly r ∣ a ↔ aeval (i (root (poly r))) a = 0
  have hdiv : poly r ∣ a ↔ minpoly K (i (root (poly r))) ∣ a :=
    Iff.of_eq (congrArg (fun b : K[X] => b ∣ a) hr)
  exact hdiv.trans minpoly.dvd_iff

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K)
  (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)
  (s : {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly s.2 ∣ h.map φ})

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "S" => AdjoinRoot (poly (Sigma.snd (Subtype.val s)))

/-- Every original top scalar factor contracts to a unique original lower scalar
factor, and the actual lower quotient embedding commutes with both original maps. -/
theorem existsUnique_lowerScalarFactor_algHom :
    ∃! r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ},
      ∃ i : AdjoinRoot (poly r.1.2) →ₐ[K] S,
        i.toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
          (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom := by
  let j : H →+* S := AdjoinRoot.map φ h (poly s.1.2) s.2
  let g : E →+* S := j.comp f.toRingHom
  have hc : g.comp (of p) = (of (poly s.1.2)).comp φ := by
    apply RingHom.ext
    intro c
    change j (f (of p c)) = of (poly s.1.2) (φ c)
    have hf : f (of p c) = of h c := by
      simpa only [AdjoinRoot.algebraMap_eq] using f.commutes c
    rw [hf]
    exact map_of φ h (poly s.1.2) s.2 c
  have hx : aeval (g (root p)) (p.map φ) = 0 := by
    rw [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq, Polynomial.eval₂_map, ← hc,
      ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  obtain ⟨r, ⟨i, hi⟩, hr⟩ := existsUnique_factor_algHom_of_root (p.map φ)
    (Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero) (g (root p)) hx
  refine ⟨r, ⟨i, ?_⟩, ?_⟩
  · apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro c
      change i (AdjoinRoot.map φ p (poly r.1.2) r.2 (of p c)) = g (of p c)
      rw [AdjoinRoot.map_of]
      exact (i.commutes (φ c)).trans (RingHom.congr_fun hc c).symm
    · change i (AdjoinRoot.map φ p (poly r.1.2) r.2 (root p)) = g (root p)
      rw [AdjoinRoot.map_root]
      exact hi
  · rintro r' ⟨i', hi'⟩
    apply hr r'
    refine ⟨i', ?_⟩
    have hroot := RingHom.congr_fun hi' (root p)
    change i' (root (poly r'.1.2)) = AdjoinRoot.map φ h (poly s.1.2) s.2 (f (root p))
    change i' (AdjoinRoot.map φ p (poly r'.1.2) r'.2 (root p)) =
      AdjoinRoot.map φ h (poly s.1.2) s.2 (f (root p)) at hroot
    rw [AdjoinRoot.map_root] at hroot
    exact hroot

/-- The preceding contraction has the exact original evaluation kernel. -/
theorem lowerScalarFactor_span_eq_ker
    (r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ})
    (i : AdjoinRoot (poly r.1.2) →ₐ[K] S)
    (hi : i.toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom) :
    Ideal.span {poly r.1.2} = RingHom.ker
      (Polynomial.eval₂RingHom (algebraMap K S)
        (AdjoinRoot.map φ h (poly s.1.2) s.2 (f (root p)))) := by
  have hroot : i (root (poly r.1.2)) =
      AdjoinRoot.map φ h (poly s.1.2) s.2 (f (root p)) := by
    have he := RingHom.congr_fun hi (root p)
    change i (AdjoinRoot.map φ p (poly r.1.2) r.2 (root p)) =
      AdjoinRoot.map φ h (poly s.1.2) s.2 (f (root p)) at he
    rw [AdjoinRoot.map_root] at he
    exact he
  rw [← hroot]
  exact factor_span_eq_ker_eval₂_of_algHom r.1.2 i

/-- The original map square also determines the lower quotient embedding itself. -/
theorem lowerScalarFactor_algHom_ext
    (r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ})
    (i₁ i₂ : AdjoinRoot (poly r.1.2) →ₐ[K] S)
    (h₁ : i₁.toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom)
    (h₂ : i₂.toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom) : i₁ = i₂ := by
  apply AdjoinRoot.algHom_ext
  have he := RingHom.congr_fun (h₁.trans h₂.symm) (root p)
  change i₁ (AdjoinRoot.map φ p (poly r.1.2) r.2 (root p)) =
    i₂ (AdjoinRoot.map φ p (poly r.1.2) r.2 (root p)) at he
  rw [AdjoinRoot.map_root] at he
  exact he

local notation "q" => towerFactor p h f
local notation "Q" => AdjoinRoot (poly q.1.2)

/-- Every original top scalar factor lifts to an actual factor of the original
relative polynomial. The actual quotient equivalence retains its lower coefficient
map, the original relative coefficient-factor square, and the original top root.
This constructs the forward pairing; it does not assert a complete index bijection. -/
theorem exists_nestedScalarFactor_quotientEquiv :
    ∃ r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ},
      ∃ i : AdjoinRoot (poly r.1.2) →ₐ[K] S,
        i.toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
          (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom ∧
        ∃ t : {t : Σ d : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly r.1.2)) d //
            poly t.2 ∣ (poly q.1.2).map (AdjoinRoot.map φ p (poly r.1.2) r.2)},
          ∃ ε : AdjoinRoot (poly t.1.2) ≃+* S,
            (∀ a : AdjoinRoot (poly r.1.2),
              ε (algebraMap (AdjoinRoot (poly r.1.2)) (AdjoinRoot (poly t.1.2)) a) =
                i a) ∧
            ε.toRingHom.comp (AdjoinRoot.map (AdjoinRoot.map φ p (poly r.1.2) r.2)
                (poly q.1.2) (poly t.1.2) t.2) =
              (AdjoinRoot.map φ h (poly s.1.2) s.2).comp
                (towerFactorRingEquiv p h f).toRingHom ∧
            ε (root (poly t.1.2)) = root (poly s.1.2) := by
  obtain ⟨r, ⟨i, hi⟩, _⟩ := existsUnique_lowerScalarFactor_algHom φ p h f s
  let R := AdjoinRoot (poly r.1.2)
  let j : E →+* R := AdjoinRoot.map φ p (poly r.1.2) r.2
  let jh : H →+* S := AdjoinRoot.map φ h (poly s.1.2) s.2
  let g : Q →+* S := jh.comp (towerFactorRingEquiv p h f).toRingHom
  have hc : g.comp (of (poly q.1.2)) = i.toRingHom.comp j := by
    apply RingHom.ext
    intro a
    change jh (towerFactorRingEquiv p h f (of (poly q.1.2) a)) = i (j a)
    have he : towerFactorRingEquiv p h f (of (poly q.1.2) a) = f a :=
      towerFactorRingEquiv_algebraMap p h f a
    rw [he]
    exact (RingHom.congr_fun hi a).symm
  have hgroot : g (root (poly q.1.2)) = root (poly s.1.2) := by
    change jh (towerFactorRingEquiv p h f (root (poly q.1.2))) = root (poly s.1.2)
    rw [towerFactorRingEquiv_root]
    exact AdjoinRoot.map_root φ h (poly s.1.2) s.2
  have hz : ((poly q.1.2).map j).eval₂ i.toRingHom (root (poly s.1.2)) = 0 := by
    rw [Polynomial.eval₂_map, ← hc, ← hgroot, ← Polynomial.hom_eval₂,
      AdjoinRoot.eval₂_root, map_zero]
  let nestedScalarAlgebra : Algebra R S := i.toRingHom.toAlgebra
  have hint : IsIntegral R (root (poly s.1.2)) :=
    (show IsAlgebraic R (root (poly s.1.2)) from
      ⟨(poly q.1.2).map j, Polynomial.map_ne_zero (ne_zero q.1.2), hz⟩).isIntegral
  let t : {t : Σ d : ℕ, MonicIrreducibleOfDegree R d //
      poly t.2 ∣ (poly q.1.2).map j} :=
    ⟨⟨(minpoly R (root (poly s.1.2))).natDegree,
      ⟨minpoly R (root (poly s.1.2)), minpoly.monic hint,
        minpoly.irreducible hint, rfl⟩⟩,
      minpoly.dvd R (root (poly s.1.2)) hz⟩
  have ht : (poly t.1.2).eval₂ i.toRingHom (root (poly s.1.2)) = 0 :=
    minpoly.aeval R (root (poly s.1.2))
  let F : AdjoinRoot (poly t.1.2) →+* S := lift i.toRingHom (root (poly s.1.2)) ht
  have hFroot : F (root (poly t.1.2)) = root (poly s.1.2) := lift_root ht
  have hFof (a : R) : F (of (poly t.1.2) a) = i a := lift_of ht
  have hcoeff : i.toRingHom.comp (of (poly r.1.2)) = of (poly s.1.2) := by
    apply RingHom.ext
    intro c
    exact i.commutes c
  have hFsurj : Function.Surjective F := by
    intro z
    obtain ⟨v, rfl⟩ := mk_surjective z
    refine ⟨mk (poly t.1.2) (v.map (of (poly r.1.2))), ?_⟩
    change lift i.toRingHom (root (poly s.1.2)) ht
      (mk (poly t.1.2) (v.map (of (poly r.1.2)))) = mk (poly s.1.2) v
    rw [lift_mk, Polynomial.eval₂_map, hcoeff, ← AdjoinRoot.algebraMap_eq,
      ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]
  let ε : AdjoinRoot (poly t.1.2) ≃+* S := RingEquiv.ofBijective F ⟨F.injective, hFsurj⟩
  refine ⟨r, i, hi, t, ε, hFof, ?_, hFroot⟩
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change F (AdjoinRoot.map j (poly q.1.2) (poly t.1.2) t.2 (of (poly q.1.2) a)) =
      g (of (poly q.1.2) a)
    rw [AdjoinRoot.map_of, hFof]
    exact (RingHom.congr_fun hc a).symm
  · change F (AdjoinRoot.map j (poly q.1.2) (poly t.1.2) t.2 (root (poly q.1.2))) =
      g (root (poly q.1.2))
    rw [AdjoinRoot.map_root, hFroot, hgroot]

end AdjoinRoot

end

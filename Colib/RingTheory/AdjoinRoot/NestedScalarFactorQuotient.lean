/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.NestedScalarFactors

/-!
# Actual quotients of nested scalar factors

Every literal lower/relative factor pair has its actual quotient generated over
`K` by the original top root. The corresponding minimal polynomial identifies
this quotient with a unique original top scalar factor. The canonical map from
the original top field and the resulting quotient equivalence retain the original
coefficient maps, lower-field map, relative map, and roots.

This module supplies the reverse quotient construction independently of the
complete dependent-index equivalence. No norm or multiplicity law is asserted.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

local instance {F : Type*} [Field F] {d : ℕ} (r : MonicIrreducibleOfDegree F d) :
    Fact (Irreducible (poly r)) := ⟨irreducible r⟩

/-- Polynomial evaluation remains in a subring containing its coefficients and root. -/
private theorem nestedFactorIndex_eval_mem {A B : Type*} [CommRing A] [CommRing B]
    (v : A →+* B) (x : B) (D : Subring B)
    (hc : ∀ a, v a ∈ D) (hx : x ∈ D) (P : A[X]) : P.eval₂ v x ∈ D := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [Polynomial.eval₂_add] using D.add_mem hP hQ
  | monomial n a =>
      simpa only [Polynomial.eval₂_monomial] using D.mul_mem (hc a) (D.pow_mem hx n)

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K)
  (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "q" => towerFactor p h f
local notation "Q" => AdjoinRoot (poly (Sigma.snd (Subtype.val q)))
local notation "Lower" =>
  {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly (Sigma.snd r) ∣ Polynomial.map φ p}
local notation "Top" =>
  {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly (Sigma.snd s) ∣ Polynomial.map φ h}
local notation "Rel" r =>
  {t : Σ d : ℕ,
      MonicIrreducibleOfDegree (AdjoinRoot (poly (Sigma.snd (Subtype.val r)))) d //
    poly (Sigma.snd t) ∣ Polynomial.map
      (AdjoinRoot.map φ p (poly (Sigma.snd (Subtype.val r))) (Subtype.property r))
      (poly (Sigma.snd (Subtype.val q)))}
local notation "Pairs" => Σ r : Lower, Rel r

/-- The original top-field map into any actual nested factor quotient. -/
def nestedScalarFactorMap (r : Lower) (t : Rel r) :
    H →+* AdjoinRoot (poly t.1.2) :=
  (AdjoinRoot.map (AdjoinRoot.map φ p (poly r.1.2) r.2)
    (poly q.1.2) (poly t.1.2) t.2).comp (towerFactorRingEquiv p h f).symm.toRingHom

/-- This map sends the original top root to the literal relative-factor root. -/
theorem nestedScalarFactorMap_root (r : Lower) (t : Rel r) :
    nestedScalarFactorMap φ p h f r t (root h) = root (poly t.1.2) := by
  have he : (towerFactorRingEquiv p h f).symm (root h) = root (poly q.1.2) := by
    apply (towerFactorRingEquiv p h f).injective
    rw [RingEquiv.apply_symm_apply, towerFactorRingEquiv_root]
  change AdjoinRoot.map (AdjoinRoot.map φ p (poly r.1.2) r.2)
    (poly q.1.2) (poly t.1.2) t.2
      ((towerFactorRingEquiv p h f).symm (root h)) = root (poly t.1.2)
  rw [he, AdjoinRoot.map_root]

/-- Original base-field coefficients follow the literal two-stage coefficient map. -/
theorem nestedScalarFactorMap_of (r : Lower) (t : Rel r) (c : k) :
    nestedScalarFactorMap φ p h f r t (of h c) =
      of (poly t.1.2) (of (poly r.1.2) (φ c)) := by
  unfold nestedScalarFactorMap
  rw [towerFactorRingEquiv_symm_toRingHom]
  simp only [RingHom.comp_apply, AdjoinRoot.map_of, AdjoinRoot.algebraMap_eq]

/-- The actual lower-field square, before choosing any top scalar factor. -/
theorem nestedScalarFactorMap_comp (r : Lower) (t : Rel r) (a : E) :
    nestedScalarFactorMap φ p h f r t (f a) =
      of (poly t.1.2) (AdjoinRoot.map φ p (poly r.1.2) r.2 a) := by
  have he : (towerFactorRingEquiv p h f).symm (f a) = of (poly q.1.2) a := by
    apply (towerFactorRingEquiv p h f).injective
    rw [RingEquiv.apply_symm_apply]
    exact (towerFactorRingEquiv_algebraMap p h f a).symm
  change AdjoinRoot.map (AdjoinRoot.map φ p (poly r.1.2) r.2)
    (poly q.1.2) (poly t.1.2) t.2
      ((towerFactorRingEquiv p h f).symm (f a)) =
        of (poly t.1.2) (AdjoinRoot.map φ p (poly r.1.2) r.2 a)
  rw [he, AdjoinRoot.map_of]

/-- A top-factor lift carrying the literal root is automatically onto the whole
actual nested quotient. Both quotient inductions use the original coefficient maps. -/
theorem nestedScalarFactor_algHom_surjective (r : Lower) (t : Rel r) (s : Top)
    (F : AdjoinRoot (poly s.1.2) →ₐ[K] AdjoinRoot (poly t.1.2))
    (hF : F (root (poly s.1.2)) = root (poly t.1.2)) : Function.Surjective F := by
  let u := nestedScalarFactorMap φ p h f r t
  let js := AdjoinRoot.map φ h (poly s.1.2) s.2
  have hsquare : F.toRingHom.comp js = u := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro c
      change F (js (of h c)) = u (of h c)
      rw [AdjoinRoot.map_of, nestedScalarFactorMap_of]
      exact F.commutes (φ c)
    · change F (js (root h)) = u (root h)
      rw [AdjoinRoot.map_root, hF, nestedScalarFactorMap_root]
  let D := F.toRingHom.range
  have hK (c : K) : of (poly t.1.2) (of (poly r.1.2) c) ∈ D :=
    ⟨of (poly s.1.2) c, F.commutes c⟩
  have hr : of (poly t.1.2) (root (poly r.1.2)) ∈ D := by
    refine ⟨js (f (root p)), ?_⟩
    have hz := RingHom.congr_fun hsquare (f (root p))
    change F (js (f (root p))) =
      nestedScalarFactorMap φ p h f r t (f (root p)) at hz
    change F (js (f (root p))) = of (poly t.1.2) (root (poly r.1.2))
    have hc := nestedScalarFactorMap_comp φ p h f r t (root p)
    rw [AdjoinRoot.map_root] at hc
    exact hz.trans hc
  have hR (a : AdjoinRoot (poly r.1.2)) : of (poly t.1.2) a ∈ D := by
    obtain ⟨v, rfl⟩ := mk_surjective a
    have hv : v.eval₂ (of (poly r.1.2)) (root (poly r.1.2)) =
        mk (poly r.1.2) v := AdjoinRoot.aeval_eq v
    have he : of (poly t.1.2) (mk (poly r.1.2) v) =
        v.eval₂ ((of (poly t.1.2)).comp (of (poly r.1.2)))
          (of (poly t.1.2) (root (poly r.1.2))) :=
      (congrArg (of (poly t.1.2)) hv).symm.trans
        (Polynomial.hom_eval₂ (p := v) (f := of (poly r.1.2))
          (g := of (poly t.1.2)) (x := root (poly r.1.2)))
    exact he.symm ▸ nestedFactorIndex_eval_mem _ _ D hK hr v
  intro z
  obtain ⟨v, rfl⟩ := mk_surjective z
  change mk (poly t.1.2) v ∈ D
  have hv : v.eval₂ (of (poly t.1.2)) (root (poly t.1.2)) =
      mk (poly t.1.2) v := AdjoinRoot.aeval_eq v
  exact hv ▸ nestedFactorIndex_eval_mem _ _ D hR ⟨root (poly s.1.2), hF⟩ v

/-- Every literal pair yields a unique original top factor, with an actual
`K`-algebra equivalence and the original root. No coverage premise is used. -/
theorem existsUnique_topScalarFactor_quotientEquiv (r : Lower) (t : Rel r) :
    ∃! s : Top, ∃ ε : AdjoinRoot (poly t.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2),
      ε (root (poly t.1.2)) = root (poly s.1.2) := by
  let u := nestedScalarFactorMap φ p h f r t
  have hc : u.comp (of h) =
      (algebraMap K (AdjoinRoot (poly t.1.2))).comp φ := by
    apply RingHom.ext
    intro c
    exact nestedScalarFactorMap_of φ p h f r t c
  have hz : aeval (root (poly t.1.2)) (h.map φ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hc,
      ← nestedScalarFactorMap_root φ p h f r t, ← Polynomial.hom_eval₂,
      AdjoinRoot.eval₂_root, map_zero]
  obtain ⟨s, ⟨F, hF⟩, hs⟩ := existsUnique_factor_algHom_of_root (h.map φ)
    (Polynomial.map_ne_zero (Fact.out : Irreducible h).ne_zero) (root (poly t.1.2)) hz
  let e := AlgEquiv.ofBijective F
    ⟨F.injective, nestedScalarFactor_algHom_surjective φ p h f r t s F hF⟩
  refine ⟨s, ⟨e.symm, ?_⟩, ?_⟩
  · apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    exact hF.symm
  · rintro s' ⟨e', he'⟩
    apply hs s'
    refine ⟨e'.symm.toAlgHom, ?_⟩
    change e'.symm (root (poly s'.1.2)) = root (poly t.1.2)
    apply e'.injective
    rw [AlgEquiv.apply_symm_apply]
    exact he'.symm

/-- A root-preserving quotient equivalence necessarily preserves the original
`H` map, original lower-field map, and original relative coefficient-factor map. -/
theorem nestedScalarFactor_quotientEquiv_squares (r : Lower) (t : Rel r) (s : Top)
    (ε : AdjoinRoot (poly t.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2))
    (hε : ε (root (poly t.1.2)) = root (poly s.1.2)) :
    ε.toRingHom.comp (nestedScalarFactorMap φ p h f r t) =
        AdjoinRoot.map φ h (poly s.1.2) s.2 ∧
    (ε.toRingHom.comp (of (poly t.1.2))).comp
        (AdjoinRoot.map φ p (poly r.1.2) r.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom ∧
    ε.toRingHom.comp (AdjoinRoot.map (AdjoinRoot.map φ p (poly r.1.2) r.2)
        (poly q.1.2) (poly t.1.2) t.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp
        (towerFactorRingEquiv p h f).toRingHom := by
  have hu : ε.toRingHom.comp (nestedScalarFactorMap φ p h f r t) =
      AdjoinRoot.map φ h (poly s.1.2) s.2 := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro c
      change ε (nestedScalarFactorMap φ p h f r t (of h c)) =
        AdjoinRoot.map φ h (poly s.1.2) s.2 (of h c)
      rw [nestedScalarFactorMap_of, AdjoinRoot.map_of]
      exact ε.commutes (φ c)
    · change ε (nestedScalarFactorMap φ p h f r t (root h)) =
        AdjoinRoot.map φ h (poly s.1.2) s.2 (root h)
      rw [nestedScalarFactorMap_root, hε, AdjoinRoot.map_root]
  refine ⟨hu, ?_, ?_⟩
  · apply RingHom.ext
    intro a
    have ha := RingHom.congr_fun hu (f a)
    change ε (nestedScalarFactorMap φ p h f r t (f a)) =
      AdjoinRoot.map φ h (poly s.1.2) s.2 (f a) at ha
    change ε (of (poly t.1.2) (AdjoinRoot.map φ p (poly r.1.2) r.2 a)) =
      AdjoinRoot.map φ h (poly s.1.2) s.2 (f a)
    rw [nestedScalarFactorMap_comp] at ha
    exact ha
  · apply RingHom.ext
    intro b
    have hb := RingHom.congr_fun hu (towerFactorRingEquiv p h f b)
    change ε (AdjoinRoot.map (AdjoinRoot.map φ p (poly r.1.2) r.2)
      (poly q.1.2) (poly t.1.2) t.2
        ((towerFactorRingEquiv p h f).symm (towerFactorRingEquiv p h f b))) =
      AdjoinRoot.map φ h (poly s.1.2) s.2 (towerFactorRingEquiv p h f b) at hb
    change ε (AdjoinRoot.map (AdjoinRoot.map φ p (poly r.1.2) r.2)
      (poly q.1.2) (poly t.1.2) t.2 b) =
      AdjoinRoot.map φ h (poly s.1.2) s.2 (towerFactorRingEquiv p h f b)
    rw [RingEquiv.symm_apply_apply] at hb
    exact hb

end AdjoinRoot

end

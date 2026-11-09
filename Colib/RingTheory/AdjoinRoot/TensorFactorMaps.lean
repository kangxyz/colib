/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.FactorIndexEquiv
public import Colib.RingTheory.AdjoinRoot.Map

/-!
# Both original field maps under the complete native factor bijection

The actual quotient equivalence attached to the complete native factor-index
bijection preserves both original coefficient maps, not only the ideals.
Consequently the original upper factor has the required linear root after the
actual opposite coefficient extension. No branch carrier or comparison hypothesis
is introduced, and no norm compatibility or multiplicity-one assertion is assumed.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

private theorem tensorFactorMaps_factor_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : R[X]) (q : S[X]) (hq : q ∣ p.map φ) (x : AdjoinRoot p) :
    (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hq) :
        AdjoinRoot (p.map φ) →+* AdjoinRoot q)
        (AdjoinRoot.map φ p (p.map φ) dvd_rfl x) = AdjoinRoot.map φ p q hq x := by
  obtain ⟨a, rfl⟩ := mk_surjective x
  rw [map_mk, map_mk]
  rfl

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "hE" => h.map (algebraMap k E)
local notation "pH" => p.map (algebraMap k H)

variable (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree (AdjoinRoot p) d //
  poly q.2 ∣ h.map (algebraMap k (AdjoinRoot p))})

/-- The complete factor bijection's actual quotient map preserves the original
first coefficient field, through the literal opposite coefficient-factor map. -/
theorem tensorSwapFactorQuotientEquiv_algebraMap (a : E) :
    tensorSwapFactorQuotientEquiv p h q (algebraMap E (AdjoinRoot (poly q.1.2)) a) =
      AdjoinRoot.map (algebraMap k H) p
        (poly (tensorSwapFactorIndexEquiv p h q).1.2)
        (tensorSwapFactorIndexEquiv p h q).2 a := by
  change tensorSwapFactorQuotientEquiv p h q
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr q.2)
        (algebraMap E (AdjoinRoot hE) a)) = _
  rw [tensorSwapFactorQuotientEquiv_factor, tensorSwapEquiv_algebraMap]
  exact tensorFactorMaps_factor_map (algebraMap k H) p
    (poly (tensorSwapFactorIndexEquiv p h q).1.2)
    (tensorSwapFactorIndexEquiv p h q).2 a

/-- The same actual quotient map preserves the second original coefficient field. -/
theorem tensorSwapFactorQuotientEquiv_map (b : H) :
    tensorSwapFactorQuotientEquiv p h q
        (AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 b) =
      algebraMap H (AdjoinRoot (poly (tensorSwapFactorIndexEquiv p h q).1.2)) b := by
  rw [← tensorFactorMaps_factor_map (algebraMap k E) h (poly q.1.2) q.2 b]
  change tensorSwapFactorQuotientEquiv p h q
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr q.2)
        (AdjoinRoot.map (algebraMap k E) h hE dvd_rfl b)) = _
  rw [tensorSwapFactorQuotientEquiv_factor, tensorSwapEquiv_map]
  rfl

/-- The upper factor root becomes precisely the original lower residue root. -/
theorem tensorSwapFactorQuotientEquiv_root :
    tensorSwapFactorQuotientEquiv p h q (root (poly q.1.2)) =
      algebraMap H (AdjoinRoot (poly (tensorSwapFactorIndexEquiv p h q).1.2)) (root h) := by
  simpa only [AdjoinRoot.map_root] using tensorSwapFactorQuotientEquiv_map p h q (root h)

/-- The original upper factor has the actual lower residue root after the
opposite coefficient extension. This is the precise linear-branch divisibility. -/
theorem tensorSwapFactor_linear_dvd :
    X - C (algebraMap H (AdjoinRoot (poly (tensorSwapFactorIndexEquiv p h q).1.2))
        (root h)) ∣
      (poly q.1.2).map
        (AdjoinRoot.map (algebraMap k H) p
          (poly (tensorSwapFactorIndexEquiv p h q).1.2)
          (tensorSwapFactorIndexEquiv p h q).2) := by
  let e := tensorSwapFactorQuotientEquiv p h q
  let φ : E →+* AdjoinRoot (poly (tensorSwapFactorIndexEquiv p h q).1.2) :=
    AdjoinRoot.map (algebraMap k H) p
      (poly (tensorSwapFactorIndexEquiv p h q).1.2)
      (tensorSwapFactorIndexEquiv p h q).2
  have hc : e.toRingHom.comp (AdjoinRoot.of (poly q.1.2)) = φ := by
    apply RingHom.ext
    intro a
    exact tensorSwapFactorQuotientEquiv_algebraMap p h q a
  have hr : e (root (poly q.1.2)) =
      algebraMap H (AdjoinRoot (poly (tensorSwapFactorIndexEquiv p h q).1.2)) (root h) :=
    tensorSwapFactorQuotientEquiv_root p h q
  have hz : (poly q.1.2).eval₂ (e.toRingHom.comp (AdjoinRoot.of (poly q.1.2)))
      (e (root (poly q.1.2))) = 0 := by
    exact (Polynomial.hom_eval₂ (poly q.1.2) (AdjoinRoot.of (poly q.1.2))
      e.toRingHom (root (poly q.1.2))).symm.trans
        (by rw [AdjoinRoot.eval₂_root, map_zero])
  rw [hc, hr] at hz
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_map]
  exact hz

end AdjoinRoot

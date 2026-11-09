module

import Colib.RingTheory.AdjoinRoot.NestedScalarFactors

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

local instance {F : Type*} [Field F] {d : ℕ} (r : MonicIrreducibleOfDegree F d) :
    Fact (Irreducible (poly r)) := ⟨irreducible r⟩

/-- The root construction uses the complete original factor index. -/
example {K L : Type*} [Field K] [Field L] [Algebra K L]
    (P : K[X]) (hP : P ≠ 0) (x : L) (hx : aeval x P = 0) :
    ∃! r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ P},
      ∃ i : AdjoinRoot (poly r.1.2) →ₐ[K] L, i (root (poly r.1.2)) = x :=
  existsUnique_factor_algHom_of_root P hP x hx

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K)
  (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)
  (s : {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly s.2 ∣ h.map φ})

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "S" => AdjoinRoot (poly (Sigma.snd (Subtype.val s)))
local notation "q" => towerFactor p h f

/-- The original lower polynomial, not a polynomial chosen after scalar extension. -/
example :
    ∃! r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ},
      ∃ i : AdjoinRoot (poly r.1.2) →ₐ[K] S,
        i.toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
          (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom :=
  existsUnique_lowerScalarFactor_algHom φ p h f s

/-- Actual field maps and the exact contracted polynomial ideal are produced together. -/
example :
    ∃ r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ},
      ∃ i : AdjoinRoot (poly r.1.2) →ₐ[K] S,
        i.toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
          (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom ∧
        Ideal.span {poly r.1.2} = RingHom.ker
          (Polynomial.eval₂RingHom (algebraMap K S)
            (AdjoinRoot.map φ h (poly s.1.2) s.2 (f (root p)))) := by
  obtain ⟨r, ⟨i, hi⟩, _⟩ := existsUnique_lowerScalarFactor_algHom φ p h f s
  exact ⟨r, i, hi, lowerScalarFactor_span_eq_ker φ p h f s r i hi⟩

/-- The same literal square determines the embedding of the same literal quotient. -/
example
    (r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ})
    (i₁ i₂ : AdjoinRoot (poly r.1.2) →ₐ[K] S)
    (h₁ : i₁.toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom)
    (h₂ : i₂.toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom) : i₁ = i₂ :=
  lowerScalarFactor_algHom_ext φ p h f s r i₁ i₂ h₁ h₂

/-- The actual quotient equivalence preserves the original K-coefficients,
original top root, and original H-map after passing through the relative quotient. -/
example :
    ∃ r : {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly r.2 ∣ p.map φ},
      ∃ t : {t : Σ d : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly r.1.2)) d //
          poly t.2 ∣ (poly q.1.2).map (AdjoinRoot.map φ p (poly r.1.2) r.2)},
        ∃ ε : AdjoinRoot (poly t.1.2) ≃+* S,
          (∀ c : K, ε (of (poly t.1.2) (of (poly r.1.2) c)) = of (poly s.1.2) c) ∧
          ε (root (poly t.1.2)) = root (poly s.1.2) ∧
          ∀ b : H,
            ε (AdjoinRoot.map (AdjoinRoot.map φ p (poly r.1.2) r.2)
              (poly q.1.2) (poly t.1.2) t.2
                (AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 b)) =
              AdjoinRoot.map φ h (poly s.1.2) s.2 b := by
  obtain ⟨r, i, _, t, ε, hcoeff, hmap, hroot⟩ :=
    exists_nestedScalarFactor_quotientEquiv φ p h f s
  refine ⟨r, t, ε, ?_, hroot, ?_⟩
  · intro c
    exact (hcoeff (of (poly r.1.2) c)).trans (i.commutes c)
  · intro b
    have hb := RingHom.congr_fun hmap
      (AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 b)
    change ε (AdjoinRoot.map (AdjoinRoot.map φ p (poly r.1.2) r.2)
      (poly q.1.2) (poly t.1.2) t.2
        (AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 b)) =
      AdjoinRoot.map φ h (poly s.1.2) s.2
        (towerFactorRingEquiv p h f
          (AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 b)) at hb
    rw [towerFactorRingEquiv_map] at hb
    exact hb

end

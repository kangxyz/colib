module

import Colib.RingTheory.AdjoinRoot.NestedScalarFactorQuotient

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

local instance {F : Type*} [Field F] {d : ℕ} (r : MonicIrreducibleOfDegree F d) :
    Fact (Irreducible (poly r)) := ⟨irreducible r⟩

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K)
  (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "q" => towerFactor p h f
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

/-- The map has the original top field as its literal domain. -/
example (r : Lower) (t : Rel r) : H →+* AdjoinRoot (poly t.1.2) :=
  nestedScalarFactorMap φ p h f r t

/-- The original top root becomes the actual upper quotient root. -/
example (r : Lower) (t : Rel r) :
    nestedScalarFactorMap φ p h f r t (root h) = root (poly t.1.2) :=
  nestedScalarFactorMap_root φ p h f r t

/-- Original k coefficients follow the actual two-stage coefficient map. -/
example (r : Lower) (t : Rel r) (c : k) :
    nestedScalarFactorMap φ p h f r t (of h c) =
      of (poly t.1.2) (of (poly r.1.2) (φ c)) :=
  nestedScalarFactorMap_of φ p h f r t c

/-- The actual lower-field square is established before choosing a top factor. -/
example (r : Lower) (t : Rel r) (a : E) :
    nestedScalarFactorMap φ p h f r t (f a) =
      of (poly t.1.2) (AdjoinRoot.map φ p (poly r.1.2) r.2 a) :=
  nestedScalarFactorMap_comp φ p h f r t a

/-- The top-factor lift covers the entire actual upper quotient. -/
example (r : Lower) (t : Rel r) (s : Top)
    (F : AdjoinRoot (poly s.1.2) →ₐ[K] AdjoinRoot (poly t.1.2))
    (hF : F (root (poly s.1.2)) = root (poly t.1.2)) : Function.Surjective F :=
  nestedScalarFactor_algHom_surjective φ p h f r t s F hF

/-- Every literal pair has a unique original top factor, with no coverage premise. -/
example (r : Lower) (t : Rel r) :
    ∃! s : Top, ∃ ε : AdjoinRoot (poly t.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2),
      ε (root (poly t.1.2)) = root (poly s.1.2) :=
  existsUnique_topScalarFactor_quotientEquiv φ p h f r t

/-- All three original map squares hold for the actual quotient equivalence. -/
example (r : Lower) (t : Rel r) (s : Top)
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
        (towerFactorRingEquiv p h f).toRingHom :=
  nestedScalarFactor_quotientEquiv_squares φ p h f r t s ε hε

end

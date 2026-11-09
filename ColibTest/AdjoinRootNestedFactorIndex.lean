module

import Colib.RingTheory.AdjoinRoot.NestedFactorIndex

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

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

/-- The reverse construction consumes every literal pair, without a coverage hypothesis. -/
example (r : Lower) (t : Rel r) :
    ∃! s : Top, ∃ ε : AdjoinRoot (poly t.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2),
      ε (root (poly t.1.2)) = root (poly s.1.2) :=
  existsUnique_topScalarFactor_quotientEquiv φ p h f r t

/-- The canonical map before selecting s already has the original lower square. -/
example (r : Lower) (t : Rel r) (a : E) :
    nestedScalarFactorMap φ p h f r t (f a) =
      of (poly t.1.2) (AdjoinRoot.map φ p (poly r.1.2) r.2 a) :=
  nestedScalarFactorMap_comp φ p h f r t a

/-- Both sides are the complete native indices, including their dependent degrees. -/
example : Top ≃ Pairs := nestedScalarFactorIndexEquiv φ p h f

/-- This equality retains the exact original top factor, not just its polynomial. -/
example (s : Top) :
    (nestedScalarFactorIndexEquiv φ p h f).symm
      (nestedScalarFactorIndexEquiv φ p h f s) = s :=
  nestedScalarFactorIndexEquiv_symm_apply_apply φ p h f s

/-- This equality retains both literal factors, not just an equivalent residue field. -/
example (r : Lower) (t : Rel r) :
    nestedScalarFactorIndexEquiv φ p h f
      ((nestedScalarFactorIndexEquiv φ p h f).symm ⟨r, t⟩) = ⟨r, t⟩ :=
  nestedScalarFactorIndexEquiv_apply_symm_apply φ p h f ⟨r, t⟩

/-- The chosen equivalence uses the actual two-stage K-algebra, without changing fields. -/
example (s : Top) (c : K) :
    let z := nestedScalarFactorIndexEquiv φ p h f s
    nestedScalarFactorQuotientEquiv φ p h f s
      (of (poly z.2.1.2) (of (poly z.1.1.2) c)) = of (poly s.1.2) c :=
  (nestedScalarFactorQuotientEquiv φ p h f s).commutes c

end

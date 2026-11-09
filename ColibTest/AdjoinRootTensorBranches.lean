module

import Colib.RingTheory.AdjoinRoot.TensorBranches

open Polynomial

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]

-- The supplied branch need not be monic, split, normal, or separable.
example (q : (AdjoinRoot p)[X]) (hqirr : Irreducible q)
    (hq : q ∣ h.map (algebraMap k (AdjoinRoot p))) :
    ∃ r : (AdjoinRoot h)[X], r.Monic ∧ Irreducible r ∧
      ∃ hr : r ∣ p.map (algebraMap k (AdjoinRoot h)),
      ∃ e : AdjoinRoot q ≃+* AdjoinRoot r,
        (∀ a : AdjoinRoot p, e (algebraMap (AdjoinRoot p) (AdjoinRoot q) a) =
          AdjoinRoot.map (algebraMap k (AdjoinRoot h)) p r hr a) ∧
        (∀ b : AdjoinRoot h,
          e (AdjoinRoot.map (algebraMap k (AdjoinRoot p)) h q hq b) =
            algebraMap (AdjoinRoot h) (AdjoinRoot r) b) :=
  AdjoinRoot.exists_tensorSwap_polynomial_branch p h q hqirr hq

-- If the whole coefficient polynomial remains irreducible, its entire original
-- field is retained rather than replaced by an abstract branch coordinate.
example (hqirr : Irreducible (h.map (algebraMap k (AdjoinRoot p)))) :
    ∃ r : (AdjoinRoot h)[X], r.Monic ∧ Irreducible r ∧
      Nonempty (AdjoinRoot (h.map (algebraMap k (AdjoinRoot p))) ≃+* AdjoinRoot r) := by
  obtain ⟨r, hrm, hri, _, e, _, _⟩ :=
    AdjoinRoot.exists_tensorSwap_polynomial_branch p h
      (h.map (algebraMap k (AdjoinRoot p))) hqirr dvd_rfl
  exact ⟨r, hrm, hri, ⟨e⟩⟩

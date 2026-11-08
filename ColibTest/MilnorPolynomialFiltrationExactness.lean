module

import Colib.RingTheory.KTheory.MilnorK.PolynomialFiltrationExactness

open Stacks.Chow

universe u

variable (k : Type u) [Field k]

-- The criterion is on the actual whole ring, without a homogeneity assumption.
example (d : ℕ) (x : MilnorKRing (RatFunc k)) :
    x ∈ milnorKPolyFiltration k d ↔
      ∀ (e : ℕ) (ψ : MonicIrreducibleOfDegree k e),
        d < e → monicIrreducibleResidue ψ x = 0 :=
  mem_milnorKPolyFiltration_iff_residue_eq_zero_above d x

-- The degree-zero filtration stage is retained, not replaced by the zero group.
example (x : MilnorKRing (RatFunc k))
    (hx : ∀ (e : ℕ) (ψ : MonicIrreducibleOfDegree k e),
      0 < e → monicIrreducibleResidue ψ x = 0) :
    x ∈ milnorKPolyFiltration k 0 :=
  mem_milnorKPolyFiltration_of_forall_monicIrreducibleResidue_eq_zero_above 0 hx

-- Every positive homogeneous degree, including source degree one, is included.
example (n d : ℕ) (x : MilnorKTheory (RatFunc k) (n + 1)) :
    (x : MilnorKRing (RatFunc k)) ∈ milnorKPolyFiltration k d ↔
      ∀ (e : ℕ) (ψ : MonicIrreducibleOfDegree k e),
        d < e → monicIrreducibleResidue ψ x = 0 :=
  mem_milnorKPolyFiltration_iff_residue_eq_zero_above d x

-- The native weak bound d corresponds to a strict source bound d + 1.
example (d e : ℕ) (ψ : MonicIrreducibleOfDegree k e) (hde : d + 1 ≤ e)
    (x : MilnorKRing (RatFunc k)) (hx : x ∈ milnorKPolyFiltration k d) :
    monicIrreducibleResidue ψ x = 0 :=
  monicIrreducibleResidue_eq_zero_of_mem_milnorKPolyFiltration_of_lt ψ hde hx

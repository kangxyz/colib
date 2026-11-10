module

import Colib.RingTheory.KTheory.MilnorK.Norm.SimpleTowerDegreeOne

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

local instance degreeOneConsumer_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

variable {k : Type u} [Field k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
  (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)
section DegreeOne

attribute [local instance] Ideal.Quotient.field

local notation "qD" => AdjoinRoot.towerFactor (poly p) (poly h) f

/-- No characteristic or ambient hypothesis is needed in the degree-one case. -/
example (hp : (poly p).natDegree = 1) :
    poly qD.1.2 = (poly h).map (algebraMap k E) :=
  towerFactor_poly_eq_map_of_lower_natDegree_eq_one p h f hp

example (hp : (poly p).natDegree = 1) (x : MilnorKRing H) :
    simpleMilnorNorm h x =
      simpleMilnorNorm p
        (simpleMilnorNorm qD.1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly qD.1.2) qD.2) x)) :=
  simpleMilnorNorm_eq_tower_of_lower_natDegree_eq_one p h f hp x

end DegreeOne

end

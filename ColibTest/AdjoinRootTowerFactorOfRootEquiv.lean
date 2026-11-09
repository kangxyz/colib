module

import Colib.RingTheory.AdjoinRoot.TowerFactorOfRootEquiv

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

attribute [local instance] AdjoinRoot.rootEquiv_nativeIrreducible

variable {K : Type*} [Field K] (r s : K[X])
  [Fact (Irreducible r)] [Fact (Irreducible s)]
  {n : ℕ} (t : MonicIrreducibleOfDegree (AdjoinRoot r) n)
  (ε : AdjoinRoot (poly t) ≃ₐ[K] AdjoinRoot s)

local notation "R" => AdjoinRoot r
local notation "T" => AdjoinRoot (poly t)
local notation "i" => ε.toAlgHom.comp (ofAlgHom K (poly t))
local notation "q" => towerFactor r s i
local notation "U" => AdjoinRoot (poly q.1.2)
local notation "θ" => towerFactorRingEquiv r s i

/-- Actual root preservation suffices for literal canonical polynomial equality. -/
example (hε : ε (root (poly t)) = root s) : poly t = poly q.1.2 :=
  rootEquiv_poly_eq_towerFactor r s t ε hε

/-- The coefficient map is exactly the identity of the original lower quotient. -/
example (hε : ε (root (poly t)) = root s) :
    poly q.1.2 ∣ (poly t).map (RingHom.id R) :=
  rootEquiv_towerFactor_dvd_map_id r s t ε hε

/-- The comparison retains both original relative quotient carriers. -/
example : T ≃+* U := rootEquivTowerRingEquiv r s t ε

/-- Coefficients are preserved pointwise, without any root assumption. -/
example (a : R) :
    rootEquivTowerRingEquiv r s t ε (algebraMap R T a) = algebraMap R U a :=
  rootEquivTowerRingEquiv_algebraMap r s t ε a

/-- The original root is preserved. -/
example (hε : ε (root (poly t)) = root s) :
    rootEquivTowerRingEquiv r s t ε (root (poly t)) = root (poly q.1.2) :=
  rootEquivTowerRingEquiv_root r s t ε hε

/-- The exact identity-coefficient quotient hom is available to native norm transport. -/
example (hε : ε (root (poly t)) = root s) :
    (rootEquivTowerRingEquiv r s t ε).toRingHom =
      AdjoinRoot.map (RingHom.id R) (poly t) (poly q.1.2)
        (rootEquiv_towerFactor_dvd_map_id r s t ε hε) :=
  rootEquivTowerRingEquiv_toRingHom r s t ε hε

/-- The actual map into the original top quotient is unchanged. -/
example : (θ).toRingHom.comp (rootEquivTowerRingEquiv r s t ε).toRingHom = ε.toRingHom :=
  rootEquivTowerRingEquiv_comp_towerFactorRingEquiv r s t ε

end

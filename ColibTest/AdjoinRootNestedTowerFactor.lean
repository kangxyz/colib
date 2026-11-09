module

import Colib.RingTheory.AdjoinRoot.NestedTowerFactor

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K)
  (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)
  (s : {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly s.2 ∣ h.map φ})

local notation "q" => towerFactor p h f

/-- There is no abstract coefficient map input: it is the actual quotient restriction. -/
example : (nestedScalarFactorLowerAlgHom φ p h f s) = ((nestedScalarFactorQuotientEquiv φ p h f
  s)).toAlgHom.comp (ofAlgHom K (poly ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2)) := rfl

/-- The polynomial identity requires no monicity assumption on the original p and h. -/
example : poly ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2 = poly (towerFactor (poly
  (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2) (nestedScalarFactorLowerAlgHom φ p h
  f s)).1.2 :=
  nestedScalarFactor_poly_eq_towerFactor φ p h f s

/-- The whole native factor index, including its degree, agrees. -/
example : ((nestedScalarFactorIndexEquiv φ p h f s).2).1 = (towerFactor (poly
  (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2) (nestedScalarFactorLowerAlgHom φ p h
  f s)).1 := nestedScalarFactor_index_eq_towerFactor φ p h f s

/-- The original relative index is equal to the canonical tower factor in its actual subtype. -/
example :
    (⟨((nestedScalarFactorIndexEquiv φ p h f s).2).1, nestedScalarFactor_dvd_top_map φ p h f s⟩ :
      {v : Σ d : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f
        s).1.1.2)) d //
        poly v.2 ∣ (poly s.1.2).map (algebraMap K (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ
          p h f s).1.1.2)))}) = (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2)
          (poly s.1.2) (nestedScalarFactorLowerAlgHom φ p h f s)) :=
  nestedScalarFactor_eq_towerFactor φ p h f s

/-- This is the exact polynomial hypothesis for native scalar polynomial transport. -/
example : poly (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
  (nestedScalarFactorLowerAlgHom φ p h f s)).1.2 = (poly ((nestedScalarFactorIndexEquiv φ p h f
  s).2).1.2).map (RingHom.id (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2))) :=
  nestedScalarFactor_towerFactor_poly_eq_map_id φ p h f s

/-- The map to use in scalar transport is the actual quotient comparison. -/
example : ((nestedScalarFactorTowerRingEquiv φ p h f s)).toRingHom =
    AdjoinRoot.map (RingHom.id (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2)))
      (poly ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2) (poly (towerFactor (poly
      (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2) (nestedScalarFactorLowerAlgHom φ
      p h f s)).1.2)
      (nestedScalarFactor_towerFactor_dvd_map_id φ p h f s) :=
  nestedScalarFactorTowerRingEquiv_toRingHom φ p h f s

/-- The original lower coefficients remain unchanged. -/
example (a : (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2))) :
  (nestedScalarFactorTowerRingEquiv φ p h f s) (of (poly ((nestedScalarFactorIndexEquiv φ p h f
  s).2).1.2) a) = of (poly (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly
  s.1.2) (nestedScalarFactorLowerAlgHom φ p h f s)).1.2) a :=
  nestedScalarFactorTowerRingEquiv_algebraMap φ p h f s a

/-- The original relative root becomes the canonical relative root. -/
example : (nestedScalarFactorTowerRingEquiv φ p h f s) (root (poly ((nestedScalarFactorIndexEquiv φ
  p h f s).2).1.2)) = root (poly (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2)
  (poly s.1.2) (nestedScalarFactorLowerAlgHom φ p h f s)).1.2) :=
  nestedScalarFactorTowerRingEquiv_root φ p h f s

/-- The canonical tower quotient returns exactly the stage 39 top quotient map. -/
example : ((towerFactorRingEquiv (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
  (nestedScalarFactorLowerAlgHom φ p h f s))).toRingHom.comp ((nestedScalarFactorTowerRingEquiv φ p
  h f s)).toRingHom = ((nestedScalarFactorQuotientEquiv φ p h f s)).toRingHom :=
  nestedScalarFactorTowerRingEquiv_comp_towerFactorRingEquiv φ p h f s

/-- The original lower-to-top scalar-factor square is retained for the actual embedding. -/
example : ((nestedScalarFactorLowerAlgHom φ p h f s)).toRingHom.comp (AdjoinRoot.map φ p (poly
  ((nestedScalarFactorIndexEquiv φ p h f s).1).1.2) ((nestedScalarFactorIndexEquiv φ p h f s).1).2)
  =
    (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom :=
  nestedScalarFactorLowerAlgHom_comp_adjoinRootMap φ p h f s

/-- The branch argument returns to the original relative/top maps, without a presentation cast. -/
example (b : AdjoinRoot (poly q.1.2)) :
    (towerFactorRingEquiv (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
      (nestedScalarFactorLowerAlgHom φ p h f s)) (AdjoinRoot.map (RingHom.id (AdjoinRoot (poly
      (nestedScalarFactorIndexEquiv φ p h f s).1.1.2))) (poly ((nestedScalarFactorIndexEquiv φ p h f
      s).2).1.2) (poly (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly
      s.1.2) (nestedScalarFactorLowerAlgHom φ p h f s)).1.2)
      (nestedScalarFactor_towerFactor_dvd_map_id φ p h f s)
        (AdjoinRoot.map (AdjoinRoot.map φ p (poly ((nestedScalarFactorIndexEquiv φ p h f s).1).1.2)
          ((nestedScalarFactorIndexEquiv φ p h f s).1).2)
          (poly q.1.2) (poly ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2)
            ((nestedScalarFactorIndexEquiv φ p h f s).2).2 b)) =
      AdjoinRoot.map φ h (poly s.1.2) s.2 (towerFactorRingEquiv p h f b) :=
  RingHom.congr_fun (nestedScalarFactor_towerFactor_map_square φ p h f s) b

end

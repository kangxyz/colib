module

import Colib.FieldTheory.AdjoinRoot.RationalCoefficientMap

noncomputable section

open Polynomial
open scoped RatFunc nonZeroDivisors
attribute [local instance] Polynomial.algebra

universe u v

variable {k : Type u} [Field k] {K : Type v} [Field K]
  (φ : k →+* K) (p : k[X]) (q : K[X])
  [Fact (Irreducible p)] [Fact (Irreducible q)]
  (hp : p.Monic) (hqmonic : q.Monic) (hq : q ∣ p.map φ)

-- The coefficient fields have independent universes and arbitrary characteristic.
example :
    (p.map (RatFunc.C : k →+* RatFunc k)).map
      (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) =
      (p.map φ).map (RatFunc.C : K →+* RatFunc K) :=
  Polynomial.map_ratFunc_C_mapRingHom φ p

example : q.map (RatFunc.C : K →+* RatFunc K) ∣
    (p.map (RatFunc.C : k →+* RatFunc k)).map
      (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) :=
  Polynomial.dvd_map_ratFunc_C_mapRingHom φ p q hq

-- No commuting-square hypothesis or separately chosen root map is supplied.
example :
    (AdjoinRoot.rationalCoefficientAlgEquiv q hqmonic).symm.toRingHom.comp
      (RatFunc.mapRingHom (Polynomial.mapRingHom (AdjoinRoot.map φ p q hq))
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom (AdjoinRoot.map φ p q hq))) =
      (AdjoinRoot.map
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))
        (p.map (RatFunc.C : k →+* RatFunc k))
        (q.map (RatFunc.C : K →+* RatFunc K))
        (Polynomial.dvd_map_ratFunc_C_mapRingHom φ p q hq)).comp
        (AdjoinRoot.rationalCoefficientAlgEquiv p hp).symm.toRingHom :=
  AdjoinRoot.rationalCoefficientAlgEquiv_symm_mapRingHom φ p q hp hqmonic hq

example [Normal k (AdjoinRoot p)] : Normal (RatFunc k) (RatFunc (AdjoinRoot p)) :=
  AdjoinRoot.normal_ratFunc_adjoinRoot p hp

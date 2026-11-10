module

import Colib.FieldTheory.AdjoinRoot.RationalCoefficient

noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

variable {k : Type*} [Field k] (p : k[X]) [Fact (Irreducible p)] (hp : p.Monic)

-- No characteristic or separability assumption is used.
example : Irreducible (p.map (RatFunc.C : k →+* RatFunc k)) :=
  hp.irreducible_map_ratFunc_C Fact.out

example : AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k)) ≃ₐ[RatFunc k]
    RatFunc (AdjoinRoot p) :=
  AdjoinRoot.rationalCoefficientAlgEquiv p hp

example : AdjoinRoot.rationalCoefficientAlgEquiv p hp
    (AdjoinRoot.root (p.map RatFunc.C)) = RatFunc.C (AdjoinRoot.root p) := by
  simp

-- The formula preserves every original coefficient-field element, not only a root.
example (x : AdjoinRoot p) : AdjoinRoot.rationalCoefficientAlgEquiv p hp
    (AdjoinRoot.map (RatFunc.C : k →+* RatFunc k) p (p.map RatFunc.C) dvd_rfl x) =
      RatFunc.C x :=
  AdjoinRoot.rationalCoefficientAlgEquiv_map p hp x

example (x : AdjoinRoot p) : (AdjoinRoot.rationalCoefficientAlgEquiv p hp).symm
    (RatFunc.C x) =
      AdjoinRoot.map (RatFunc.C : k →+* RatFunc k) p (p.map RatFunc.C) dvd_rfl x :=
  AdjoinRoot.rationalCoefficientAlgEquiv_symm_C p hp x

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.IrreducibleLocalMap

open Polynomial IsLocalRing

noncomputable section

attribute [local instance] Polynomial.irreducibleLocalMap_isPrime

variable {k B : Type*} [Field k] [CommRing B] [IsLocalRing B]
  (q : k[X]) [Fact (Irreducible q)]
  (c : k →+* B) (t : B) (hq : residue B (q.eval₂ c t) = 0)

example (a : k[X]) : residue B (a.eval₂ c t) = 0 ↔ q ∣ a :=
  residue_eval₂_eq_zero_iff_dvd q c t hq a

example (a : k[X]) : IsUnit (a.eval₂ c t) ↔ a ∉ Ideal.span ({q} : Set k[X]) :=
  isUnit_eval₂_iff_not_mem_span_irreducible q c t hq a

example (a : k[X]) :
    localizeAtIrreducibleEval₂ q c t hq
        (algebraMap k[X] (Localization.AtPrime (Ideal.span ({q} : Set k[X]))) a) =
      a.eval₂ c t :=
  localizeAtIrreducibleEval₂_algebraMap q c t hq a

example : IsLocalHom (localizeAtIrreducibleEval₂ q c t hq) :=
  isLocalHom_localizeAtIrreducibleEval₂ q c t hq

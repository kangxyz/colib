module

import Colib.RingTheory.Polynomial.OriginLocalMap

noncomputable section

open Polynomial IsLocalRing

variable {k B : Type*} [Field k] [CommRing B] [IsLocalRing B]

local instance : (Ideal.span ({X} : Set k[X])).IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero : (X : k[X]) ≠ 0)).mpr prime_X

example (c : k →+* B) {t : B} (ht : t ∈ maximalIdeal B) :
    IsLocalHom (localizeAtOriginEval₂ c ht) :=
  isLocalHom_localizeAtOriginEval₂ c ht

example (c : k →+* B) {t : B} (ht : t ∈ maximalIdeal B) (q : k[X]) :
    residue B (localizeAtOriginEval₂ c ht
        (algebraMap k[X] (Localization.AtPrime (Ideal.span ({X} : Set k[X]))) q)) =
      residue B (c (q.coeff 0)) :=
  residue_localizeAtOriginEval₂_algebraMap c ht q

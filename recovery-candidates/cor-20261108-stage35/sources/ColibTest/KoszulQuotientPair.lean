/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.RingTheory.Koszul.QuotientPair

noncomputable section

open CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

variable (A : Type u) [CommRing A] (I J : Ideal A)

example :
    (((Tor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I))).obj
      (ModuleCat.of A (A ⧸ J))) ≅ ModuleCat.of A (A ⧸ I ⊔ J) :=
  torZeroQuotientQuotientIso A I J

example (t s : List A) (hs : IsRegular A s) (hts : IsRegular A (t ++ s))
    (hI : I = Ideal.ofList t) (hJ : J = Ideal.ofList s) (n : ℕ) (hn : n ≠ 0) :
    IsZero (((Tor (ModuleCat A) n).obj (ModuleCat.of A (A ⧸ J))).obj
      (ModuleCat.of A (A ⧸ I))) :=
  Koszul.isZero_tor_quotients_of_regular_append A t s hs hts I J hI hJ n hn

example (s : List A) (hs : IsRegular A s) (n : ℕ) (hn : n ≠ 0) :
    IsZero (((Tor (ModuleCat A) n).obj (ModuleCat.of A (A ⧸ Ideal.ofList s))).obj
      (ModuleCat.of A (A ⧸ Ideal.ofList ([] : List A)))) :=
  Koszul.isZero_tor_quotients_of_regular_append A [] s hs (by simpa using hs)
    (Ideal.ofList ([] : List A)) (Ideal.ofList s) rfl rfl n hn

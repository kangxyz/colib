/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Dedekind.ResidueSupport

/-! Full-statement consumers of native finite support in arbitrary characteristic. -/

noncomputable section

open Stacks.Chow Stacks.Chow.DedekindResidue IsDedekindDomain IsLocalRing

variable (S E : Type*) [CommRing S] [IsDedekindDomain S]
  [Field E] [Algebra S E] [IsFractionRing S E]

example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    Set.Finite {q : HeightOneSpectrum S |
      dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n x ≠ 0} :=
  finite_residue_support S E n x

example (n : ℕ) (x : MilnorKTheory E (n + 1)) (q : HeightOneSpectrum S) :
    totalResidue S E n x q = dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n x :=
  totalResidue_apply S E n x q

example (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    totalResidue S E n x = 0 ↔ ∀ q : HeightOneSpectrum S,
      dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n x = 0 :=
  totalResidue_eq_zero_iff S E n x

example (x : MilnorKTheory E 1) :
    Set.Finite {q : HeightOneSpectrum S |
      dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E 0 x ≠ 0} :=
  finite_residue_support S E 0 x

end

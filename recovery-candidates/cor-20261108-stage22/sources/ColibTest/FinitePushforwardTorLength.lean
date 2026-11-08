module

import Colib.Algebra.Category.ModuleCat.Tor.FinitePushforward

open CategoryTheory

universe u

#check HomologicalComplex.length_homology_finitePushforward_eq_sum
#check HomologicalComplex.sum_alternating_lengthToNat_homology_finitePushforward
#check ModuleCat.Tor.finitePushforwardResolutionHomologyIso
#check ModuleCat.Tor.length_finitePushforward_eq_sum
#check ModuleCat.Tor.sum_alternating_lengthToNat_finitePushforwardResolutionHomology

/-- The module-level theorem needs neither a domain nor reducedness nor flatness of the finite
algebra. In particular the arbitrary finite algebra keeps every maximal label over the one
closed base point. -/
example (R S : Type u) [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] [Fintype (MaximalSpectrum S)]
    (M N : ModuleCat.{u} S) (n : ℕ) :
    Module.length R ((HomologicalComplex.finitePushforwardComplex R S
      (ModuleCat.Tor.resolutionTensorComplex S M N)).homology n) =
      Module.length R ((ModuleCat.restrictScalars (algebraMap R S)).obj
        (((Tor (ModuleCat.{u} S) n).obj M).obj N)) :=
  (ModuleCat.Tor.finitePushforwardResolutionHomologyIso R S M N n).toLinearEquiv.length_eq

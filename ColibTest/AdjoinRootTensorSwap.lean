module

import Colib.RingTheory.AdjoinRoot.TensorSwap

noncomputable section

open Polynomial
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

-- No field or irreducibility assumption is used, even for the whole algebra.
example (p : R[X]) : S ⊗[R] AdjoinRoot p ≃ₐ[S] AdjoinRoot (p.map (algebraMap R S)) :=
  AdjoinRoot.scalarExtensionEquiv p

example (p h : R[X]) (a : AdjoinRoot p) :
    AdjoinRoot.tensorSwapEquiv p h
        (algebraMap (AdjoinRoot p) (AdjoinRoot (h.map (algebraMap R (AdjoinRoot p)))) a) =
      AdjoinRoot.map (algebraMap R (AdjoinRoot h)) p
        (p.map (algebraMap R (AdjoinRoot h))) dvd_rfl a :=
  AdjoinRoot.tensorSwapEquiv_algebraMap p h a

-- Every maximal ideal is retained, not just a chosen split polynomial factor.
example (p h : R[X])
    (m : MaximalSpectrum (AdjoinRoot (h.map (algebraMap R (AdjoinRoot p))))) :
    (AdjoinRoot.tensorSwapMaximalEquiv p h).symm
      (AdjoinRoot.tensorSwapMaximalEquiv p h m) = m :=
  (AdjoinRoot.tensorSwapMaximalEquiv p h).symm_apply_apply m

example (p h : R[X])
    (m : MaximalSpectrum (AdjoinRoot (h.map (algebraMap R (AdjoinRoot p)))))
    (a : AdjoinRoot p) :
    AdjoinRoot.tensorSwapQuotientEquiv p h m
        (Ideal.Quotient.mk m.asIdeal
          (algebraMap (AdjoinRoot p) (AdjoinRoot (h.map (algebraMap R (AdjoinRoot p)))) a)) =
      Ideal.Quotient.mk (AdjoinRoot.tensorSwapMaximalEquiv p h m).asIdeal
        (AdjoinRoot.map (algebraMap R (AdjoinRoot h)) p
          (p.map (algebraMap R (AdjoinRoot h))) dvd_rfl a) :=
  AdjoinRoot.tensorSwapQuotientEquiv_algebraMap p h m a

example (p h : R[X])
    (m : MaximalSpectrum (AdjoinRoot (h.map (algebraMap R (AdjoinRoot p)))))
    (b : AdjoinRoot h) :
    AdjoinRoot.tensorSwapQuotientEquiv p h m
        (Ideal.Quotient.mk m.asIdeal
          (AdjoinRoot.map (algebraMap R (AdjoinRoot p)) h
            (h.map (algebraMap R (AdjoinRoot p))) dvd_rfl b)) =
      Ideal.Quotient.mk (AdjoinRoot.tensorSwapMaximalEquiv p h m).asIdeal
        (algebraMap (AdjoinRoot h) (AdjoinRoot (p.map (algebraMap R (AdjoinRoot h)))) b) :=
  AdjoinRoot.tensorSwapQuotientEquiv_map p h m b

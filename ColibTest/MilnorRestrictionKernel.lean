module

import Colib.RingTheory.KTheory.MilnorK.RestrictionKernel

open Stacks.Chow

universe u

variable (k E L : Type u) [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra k L] [FiniteDimensional k E] [FiniteDimensional k L]

-- No separability or characteristic instance is required for the degree retraction.
example (n : ℕ) (x : MilnorKTheory k n) :
    milnorKNorm k E n (milnorKTransport (algebraMap k E) n x) =
      (Module.finrank k E : ℤ) • x :=
  milnorKNorm_milnorKTransport k E n x

example (x : MilnorKRing k) (hx : milnorKRingMap (algebraMap k E) x = 0) :
    (Module.finrank k E : ℤ) • x = 0 :=
  finrank_zsmul_eq_zero_of_milnorKRingMap_eq_zero k E x hx

-- The two overfields are unrelated except for their common base.
example (h : (Module.finrank k E).Coprime (Module.finrank k L))
    (x : MilnorKRing k) (hE : milnorKRingMap (algebraMap k E) x = 0)
    (hL : milnorKRingMap (algebraMap k L) x = 0) : x = 0 :=
  eq_zero_of_two_milnorKRingMaps_eq_zero_of_coprime k E L h x hE hL

-- Degree zero is not omitted from homogeneous detection.
example (h : (Module.finrank k E).Coprime (Module.finrank k L))
    (x : MilnorKTheory k 0) (hE : milnorKTransport (algebraMap k E) 0 x = 0)
    (hL : milnorKTransport (algebraMap k L) 0 x = 0) : x = 0 :=
  eq_zero_of_two_milnorKTransports_eq_zero_of_coprime k E L h 0 x hE hL

example (n p r : ℕ) (hp : p.Coprime (Module.finrank k E)) (x : MilnorKTheory k n)
    (hx : milnorKTransport (algebraMap k E) n x = 0)
    (hxp : ((p ^ r : ℕ) : ℤ) • x = 0) : x = 0 :=
  eq_zero_of_milnorKTransport_eq_zero_of_coprime_pow k E n p r hp x hx hxp

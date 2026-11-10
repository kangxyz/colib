module

import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenEquivariance

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

example
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
    [CharZero k] (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing k L x) =
      milnorKNormRing k' L' (milnorKRingMap τ.toRingHom x) :=
  milnorKNormRing_map_ringEquiv σ τ hστ x

example
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
    [CharZero k] (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) :
    (milnorKRingMap σ.toRingHom).toAddMonoidHom.comp (milnorKNormRing k L) =
      (milnorKNormRing k' L').comp (milnorKRingMap τ.toRingHom).toAddMonoidHom :=
  milnorKNormRing_comp_map_ringEquiv σ τ hστ

example
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
    [CharZero k] (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport σ.toRingHom n (milnorKNorm k L n x) =
      milnorKNorm k' L' n (milnorKTransport τ.toRingHom n x) :=
  milnorKNorm_map_ringEquiv σ τ hστ n x

example
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
    [CharZero k] (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) :
    (milnorKTransport σ.toRingHom n).comp (milnorKNorm k L n) =
      (milnorKNorm k' L' n).comp (milnorKTransport τ.toRingHom n) :=
  milnorKNorm_comp_map_ringEquiv σ τ hστ n

end

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparison
public import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentationEquivariance
public import Mathlib.Algebra.Ring.CharZero

/-!
# Simultaneous base and extension equivariance of the native chosen norm

The field equivalences commute with the original algebra actions. An actual
polynomial presentation is transported by its coefficient map and quotient map.
The original simple norm coefficient square and chosen comparison then give the
whole-ring square. No transported scalar action or replacement norm is defined.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The original finite chosen norm commutes with a simultaneous isomorphism of
its base and extension fields, with the original structure maps on both sides. -/
theorem milnorKNormRing_map_ringEquiv
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
    [CharZero k] (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (x : MilnorKRing L) :
    milnorKRingMap σ.toRingHom (milnorKNormRing k L x) =
      milnorKNormRing k' L' (milnorKRingMap τ.toRingHom x) := by
  let hCharZero : CharZero k' := σ.symm.toRingHom.charZero
  obtain ⟨d, p, ⟨f⟩⟩ := exists_monicIrreducible_presentation k L
  obtain ⟨q, g, hq, hmap⟩ :=
    exists_monicIrreducible_presentation_ringEquiv σ τ hστ p f
  have hleft := congrArg (milnorKRingMap σ.toRingHom)
    (milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv p f x)
  have hsimple := simpleMilnorNorm_map_of_poly_eq_map σ.toRingHom p q hq
    (milnorKRingMap f.toRingHom x)
  have hcompLeft := milnorKRingMap_comp_apply f.toRingHom
    (AdjoinRoot.map σ.toRingHom (poly p) (poly q) (hq ▸ dvd_rfl)) x
  have hmaps := congrArg
    (fun ψ : L →+* AdjoinRoot (poly q) => milnorKRingMap ψ x) hmap
  have hcompRight := milnorKRingMap_comp_apply τ.toRingHom g.toRingHom x
  have hvalues := hcompLeft.trans (hmaps.trans hcompRight.symm)
  have hnorm := congrArg (simpleMilnorNorm q) hvalues
  have hright := milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv q g
    (milnorKRingMap τ.toRingHom x)
  exact hleft.trans (hsimple.trans (hnorm.trans hright.symm))

/-- The simultaneous equivalence square as equality of the original additive maps. -/
theorem milnorKNormRing_comp_map_ringEquiv
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
    [CharZero k] (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) :
    (milnorKRingMap σ.toRingHom).toAddMonoidHom.comp (milnorKNormRing k L) =
      (milnorKNormRing k' L').comp (milnorKRingMap τ.toRingHom).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNormRing_map_ringEquiv σ τ hστ x

/-- Simultaneous equivariance on every actual homogeneous Milnor group. -/
theorem milnorKNorm_map_ringEquiv
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
    [CharZero k] (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTransport σ.toRingHom n (milnorKNorm k L n x) =
      milnorKNorm k' L' n (milnorKTransport τ.toRingHom n x) := by
  apply Subtype.ext
  exact milnorKNormRing_map_ringEquiv σ τ hστ (x : MilnorKRing L)

/-- Simultaneous equivariance as equality of the original homogeneous additive maps. -/
theorem milnorKNorm_comp_map_ringEquiv
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L'] [FiniteDimensional k L] [FiniteDimensional k' L']
    [CharZero k] (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom) (n : ℕ) :
    (milnorKTransport σ.toRingHom n).comp (milnorKNorm k L n) =
      (milnorKNorm k' L' n).comp (milnorKTransport τ.toRingHom n) := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNorm_map_ringEquiv σ τ hστ n x

end Stacks.Chow

end

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.AdjoinRoot.RationalCoefficientMap
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Constant automorphisms on the original rational function fields

The existing fraction-field lift extends a polynomial coefficient automorphism.
Its underlying ring homomorphism is the original `RatFunc.mapRingHom`, proved by
localization extensionality. For a finite Galois simple constant field the lift
is a bijection on the actual Galois groups: injectivity is detected on constants,
and the two native extension degrees agree.
-/

@[expose] public noncomputable section

open Polynomial Module
open scoped RatFunc nonZeroDivisors
attribute [local instance] Polynomial.algebra

namespace RatFunc

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/-- The polynomial coefficient automorphism fixes the original base polynomial ring. -/
def coefficientPolynomialAlgEquiv (σ : Gal(E/k)) : E[X] ≃ₐ[k[X]] E[X] :=
  { Polynomial.mapEquiv σ.toRingEquiv with
    commutes' := fun a => by
      change (a.map (algebraMap k E)).map σ.toRingHom = a.map (algebraMap k E)
      rw [Polynomial.map_map]
      exact congrArg (fun φ : k →+* E => a.map φ)
        (by ext x; exact σ.commutes x) }

/-- The native fraction-field lift of an actual coefficient automorphism. -/
def coefficientGal (σ : Gal(E/k)) : Gal((RatFunc E)/(RatFunc k)) :=
  IsFractionRing.fieldEquivOfAlgEquiv (RatFunc k) (RatFunc E) (RatFunc E)
    (coefficientPolynomialAlgEquiv σ)

/-- The lifted automorphism is literally the native rational coefficient map. -/
theorem coefficientGal_toRingHom (σ : Gal(E/k)) :
    (coefficientGal σ).toRingHom =
      RatFunc.mapRingHom (Polynomial.mapRingHom σ.toRingHom)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom σ.toRingHom) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors E[X])
  apply RingHom.ext
  intro a
  change coefficientGal σ (algebraMap E[X] (RatFunc E) a) = _
  rw [coefficientGal, IsFractionRing.fieldEquivOfAlgEquiv_algebraMap,
    RingHom.comp_apply, RatFunc.mapRingHom_algebraMap]
  rfl

/-- The lifted automorphism retains every actual coefficient. -/
@[simp]
theorem coefficientGal_C (σ : Gal(E/k)) (a : E) :
    coefficientGal σ (RatFunc.C a) = RatFunc.C (σ a) := by
  change (coefficientGal σ).toRingHom (RatFunc.C a) = _
  rw [coefficientGal_toRingHom, RatFunc.mapRingHom_coefficient_C]
  rfl

/-- Constant extension is injective on the actual Galois automorphisms. -/
theorem coefficientGal_injective :
    Function.Injective (coefficientGal : Gal(E/k) → Gal((RatFunc E)/(RatFunc k))) := by
  intro σ τ h
  apply AlgEquiv.ext
  intro a
  apply (RatFunc.C : E →+* RatFunc E).injective
  simpa only [coefficientGal_C] using DFunLike.congr_fun h (RatFunc.C a)

/-- If the constant and rational extensions are Galois, every rational automorphism
is the lift of an actual constant automorphism. The equality of native extension
degrees is proved, not assumed as abstract comparison data. -/
theorem coefficientGal_bijective [FiniteDimensional k E] [IsGalois k E]
    [IsGalois (RatFunc k) (RatFunc E)] :
    Function.Bijective (coefficientGal : Gal(E/k) → Gal((RatFunc E)/(RatFunc k))) := by
  let : FiniteDimensional (RatFunc k) (RatFunc E) :=
    FiniteDimensional.of_finrank_pos (by
      rw [RatFunc.finrank_ratFunc_ratFunc]
      exact Module.finrank_pos)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨coefficientGal_injective, ?_⟩
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
    IsGalois.card_aut_eq_finrank k E,
    IsGalois.card_aut_eq_finrank (RatFunc k) (RatFunc E),
    RatFunc.finrank_ratFunc_ratFunc]

end RatFunc

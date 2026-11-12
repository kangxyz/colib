/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatProduct
public import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal

/-!
# Ideal products of whole finite-flat closed schemes

A literal product of ideal sheaves gives a full fundamental-cycle sum when the
first ideal is locally principal, the second is effective Cartier, and all
three support schemes are finite flat over the source. Actual affine-local
regular equations supply the local multiplication sequence. Generic quotient
lengths are finite; flatness eliminates non-generic source contributions.
No integrality or reducedness of the ambient scheme is used.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Divisors

universe u

namespace Stacks.Chow

variable {C X : Scheme.{u}}

/-- Local principality supplies an actual generator of each original ideal stalk. -/
theorem exists_stalk_span_of_locallyPrincipal (I : C.IdealSheafData)
    (hI : IsLocallyPrincipal I) (x : C) :
    ∃ a : C.presheaf.stalk x, IdealSheafData.stalk I x = Ideal.span {a} := by
  obtain ⟨U, hx, hU⟩ := hI x
  obtain ⟨a, ha⟩ := hU.principal
  refine ⟨(C.presheaf.germ U.1 x hx).hom a, ?_⟩
  rw [IdealSheafData.stalk_eq_map_germ I x U hx, ha, Ideal.map_span, Set.image_singleton]

/-- An effective Cartier ideal has an actual regular stalk generator without
any integral-ambient assumption. -/
theorem exists_stalk_regular_span_of_effectiveCartier (J : C.IdealSheafData)
    (hJ : IsEffectiveCartierDivisor J) (x : C) :
    ∃ b : C.presheaf.stalk x,
      IdealSheafData.stalk J x = Ideal.span {b} ∧
        b ∈ nonZeroDivisors (C.presheaf.stalk x) := by
  obtain ⟨U, hU, hx, b, hb, he⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor J hJ x
  refine ⟨(C.presheaf.germ U x hx).hom b, ?_, germ_mem_nonZeroDivisors hU hb x hx⟩
  rw [IdealSheafData.stalk_eq_map_germ J x ⟨U, hU⟩ hx, he,
    Ideal.map_span, Set.image_singleton]

/-- Full product-cycle additivity for actual finite-flat supports. All scheme
structures and generic nilpotent lengths are preserved. -/
theorem finiteCyclePushforward_fundamentalCycle_add_of_ideal_product
    [IsNoetherian X] (p : C ⟶ X) (I J K : C.IdealSheafData)
    [IsFinite (I.subschemeι ≫ p)] [IsFinite (J.subschemeι ≫ p)]
    [IsFinite (K.subschemeι ≫ p)]
    [Flat (I.subschemeι ≫ p)] [Flat (J.subschemeι ≫ p)] [Flat (K.subschemeι ≫ p)]
    (hI : IsLocallyPrincipal I) (hJ : IsEffectiveCartierDivisor J) (hK : K = I * J) :
    letI := Scheme.isNoetherian_of_finiteType (I.subschemeι ≫ p)
    letI := Scheme.isNoetherian_of_finiteType (J.subschemeι ≫ p)
    letI := Scheme.isNoetherian_of_finiteType (K.subschemeι ≫ p)
    finiteCyclePushforward K.subschemeι (AlgebraicCycle.fundamentalCycle K.subscheme) =
      finiteCyclePushforward I.subschemeι (AlgebraicCycle.fundamentalCycle I.subscheme) +
        finiteCyclePushforward J.subschemeι (AlgebraicCycle.fundamentalCycle J.subscheme) := by
  have := Scheme.isNoetherian_of_finiteType (I.subschemeι ≫ p)
  have := Scheme.isNoetherian_of_finiteType (J.subschemeι ≫ p)
  have := Scheme.isNoetherian_of_finiteType (K.subschemeι ≫ p)
  apply finiteCyclePushforward_fundamentalCycle_mul_of_stalk_ker
    p I.subschemeι J.subschemeι K.subschemeι
  intro x hx
  obtain ⟨a, ha⟩ := exists_stalk_span_of_locallyPrincipal I hI x
  obtain ⟨b, hb, hreg⟩ := exists_stalk_regular_span_of_effectiveCartier J hJ x
  refine ⟨a, b, ?_, ?_, ?_, hreg⟩
  · simpa only [Scheme.IdealSheafData.ker_subschemeι] using ha
  · simpa only [Scheme.IdealSheafData.ker_subschemeι] using hb
  · rw [Scheme.IdealSheafData.ker_subschemeι, hK, IdealSheafData.stalk_mul, ha, hb,
      Ideal.span_singleton_mul_span_singleton]

end Stacks.Chow

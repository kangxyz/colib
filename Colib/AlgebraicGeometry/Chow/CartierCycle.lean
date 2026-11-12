/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction
public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointCycle
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Sum
public import StacksFrontier.AlgebraicGeometry.F6Rank89.StalkDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# Whole Cartier zero schemes and their cycle coefficients

The cycle is the actual closed pushforward of the fundamental cycle of the
zero scheme. Its coefficients are the quotient-stalk lengths, unchanged
on an open chart and additive for products of Cartier ideals.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order Stacks.Chow Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsNoetherian X]

local instance (I : X.IdealSheafData) : IsNoetherian I.subscheme :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace I.subschemeι }

/-- The original fundamental cycle of the actual closed subscheme. -/
abbrev cartierCycle (I : X.IdealSheafData) : AlgebraicCycle X ℤ :=
  finiteCyclePushforward I.subschemeι (AlgebraicCycle.fundamentalCycle I.subscheme)

private theorem genericPoint_of_cartier_coheight_one (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) (y : I.subscheme)
    (hy : coheight (I.subschemeι y) = 1) : y ∈ genericPoints I.subscheme := by
  apply AlgebraicCycle.mem_genericPoints_of_stalk_length_ne_top
  rw [← closedImmersionQuotientStalkLength_image I.subschemeι y,
    closedImmersionQuotientStalkLength, IdealSheafData.ker_subschemeι]
  let x := I.subschemeι y
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hy.le
  obtain ⟨a, ha, he⟩ :=
    Stacks.Divisors.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor I hI x
  change Module.length (X.presheaf.stalk x)
    ((X.presheaf.stalk x) ⧸ IdealSheafData.stalk I x) ≠ ⊤
  rw [he]
  exact Module.length_ne_top_iff.mpr
    (isFiniteLength_quotient_span_singleton (X.presheaf.stalk x) ha.mem_nonZeroDivisors)

private theorem coheight_one_of_cartier_genericPoint (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) (y : I.subscheme) (hy : y ∈ genericPoints I.subscheme) :
    coheight (I.subschemeι y) = 1 := by
  have hzero := (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints I.subscheme y).mpr hy
  have h := ringKrullDim_stalk_subscheme_add_one I hI y
  rw [hzero, zero_add, ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h.symm

/-- At an ambient coheight-one point the coefficient is the full quotient
length of the actual stalk ideal. -/
theorem cartierCycle_apply_coheight_one (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) (x : X) (hx : coheight x = 1) :
    cartierCycle I x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ IdealSheafData.stalk I x)).toNat : ℤ) := by
  rw [cartierCycle, AlgebraicCycle.fundamentalCycle_pushforward_closed_apply _ _ (by
      intro y hy
      exact genericPoint_of_cartier_coheight_one I hI y (hy.symm ▸ hx)),
    closedImmersionQuotientStalkLength, IdealSheafData.ker_subschemeι]

/-- The actual Cartier zero cycle is supported at coheight one. -/
theorem cartierCycle_apply_coheight_ne_one (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) (x : X) (hx : coheight x ≠ 1) :
    cartierCycle I x = 0 :=
  AlgebraicCycle.fundamentalCycle_pushforward_closed_eq_zero _ _ fun y hy hgen ↦
    hx (hy ▸ coheight_one_of_cartier_genericPoint I hI y hgen)

/-- The full coefficient is unchanged by restricting to the actual open chart. -/
theorem cartierCycle_apply_of_isOpenImmersion {Y : Scheme.{u}} [IsNoetherian Y]
    (I : X.IdealSheafData) (hI : IsEffectiveCartierDivisor I)
    (v : Y ⟶ X) [IsOpenImmersion v] (y : Y) :
    cartierCycle (I.comap v) y = cartierCycle I (v y) := by
  have hJ := isPullbackDefined_of_flat v I hI
  have hcy : coheight (v y) = coheight y := coheight_eq_of_isOpenImmersion v
  by_cases hy : coheight y = 1
  · rw [cartierCycle_apply_coheight_one _ hJ _ hy,
      cartierCycle_apply_coheight_one I hI _ (hcy.trans hy)]
    have h := Module.quotient_length_eq_of_ringEquiv
      (asIso (v.stalkMap y)).commRingCatIsoToRingEquiv (IdealSheafData.stalk I (v y))
    change Module.length (X.presheaf.stalk (v y))
      ((X.presheaf.stalk (v y)) ⧸ IdealSheafData.stalk I (v y)) =
      Module.length (Y.presheaf.stalk y)
        ((Y.presheaf.stalk y) ⧸ (IdealSheafData.stalk I (v y)).map (v.stalkMap y).hom) at h
    rw [← IdealSheafData.stalk_comap I v y] at h
    exact congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ)) h.symm
  · rw [cartierCycle_apply_coheight_ne_one _ hJ _ hy,
      cartierCycle_apply_coheight_ne_one I hI _ (fun h ↦ hy (hcy.symm.trans h))]

/-- Multiplying the two original Cartier ideals adds the two full cycles. -/
theorem cartierCycle_mul (I J : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) (hJ : IsEffectiveCartierDivisor J) :
    cartierCycle (I * J) = cartierCycle I + cartierCycle J := by
  have hIJ := isEffectiveCartierDivisor_mul I J hI hJ
  apply Function.locallyFinsuppWithin.ext
  intro x
  change cartierCycle (I * J) x = cartierCycle I x + cartierCycle J x
  by_cases hx : coheight x = 1
  · let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    obtain ⟨a, ha, hIa⟩ :=
      Stacks.Divisors.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor I hI x
    obtain ⟨b, hb, hJb⟩ :=
      Stacks.Divisors.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor J hJ x
    have hfa := Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton (X.presheaf.stalk x) ha.mem_nonZeroDivisors)
    have hfb := Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton (X.presheaf.stalk x) hb.mem_nonZeroDivisors)
    change Ring.ord (X.presheaf.stalk x) a ≠ ⊤ at hfa
    change Ring.ord (X.presheaf.stalk x) b ≠ ⊤ at hfb
    rw [cartierCycle_apply_coheight_one _ hIJ _ hx, cartierCycle_apply_coheight_one I hI _ hx,
      cartierCycle_apply_coheight_one J hJ _ hx, AlgebraicGeometry.IdealSheafData.stalk_mul,
      hIa, hJb, Ideal.span_singleton_mul_span_singleton]
    change ((Ring.ord (X.presheaf.stalk x) (a * b)).toNat : ℤ) = _
    rw [Ring.ord_mul _ hb.mem_nonZeroDivisors, ENat.toNat_add hfa hfb, Nat.cast_add]
    rfl
  · rw [cartierCycle_apply_coheight_ne_one _ hIJ _ hx,
      cartierCycle_apply_coheight_ne_one I hI _ hx, cartierCycle_apply_coheight_ne_one J hJ _ hx,
      zero_add]

/-- A closed immersion already presents the same cycle as its literal
kernel subscheme. -/
theorem cartierCycle_ker_eq_pushforward {Y : Scheme.{u}} [IsNoetherian Y] (i : Y ⟶ X)
    [IsClosedImmersion i] :
    cartierCycle i.ker = finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle Y) := by
  let e : Y ≅ i.ker.subscheme := asIso i.toImage
  have he : e.hom ≫ i.ker.subschemeι = i := i.toImage_imageι
  change finiteCyclePushforward i.ker.subschemeι (AlgebraicCycle.fundamentalCycle _) = _
  rw [← finiteCyclePushforward_fundamentalCycle_iso e, finiteCyclePushforward_comp_apply]
  exact finiteCyclePushforward_congr _ _ he _

/-- The cycle of a whole zero scheme mapped into an open has the same
coefficients as its pushforward on the ambient target. -/
theorem finiteCyclePushforward_cartierCycle_apply_of_supportIso
    {Y W D : Scheme.{u}} [IsNoetherian D] (I : X.IdealSheafData)
    (f : X ⟶ Y) [IsFinite f] (i : W ⟶ Y) [IsOpenImmersion i]
    (g : D ⟶ W) [IsFinite g] (e : D ≅ I.subscheme)
    (h : g ≫ i = e.hom ≫ I.subschemeι ≫ f) (w : W) :
    finiteCyclePushforward f (cartierCycle I) (i w) =
      finiteCyclePushforward g (AlgebraicCycle.fundamentalCycle D) w := by
  let : IsFinite (g ≫ i) := h.symm ▸ inferInstanceAs (IsFinite (e.hom ≫ I.subschemeι ≫ f))
  rw [← finiteCyclePushforward_comp_open_apply g i]
  have he : finiteCyclePushforward f (cartierCycle I) =
      finiteCyclePushforward (g ≫ i) (AlgebraicCycle.fundamentalCycle D) := by
    change finiteCyclePushforward f
      (finiteCyclePushforward I.subschemeι (AlgebraicCycle.fundamentalCycle I.subscheme)) = _
    rw [← finiteCyclePushforward_fundamentalCycle_iso e, finiteCyclePushforward_comp_apply,
      finiteCyclePushforward_comp_apply]
    exact finiteCyclePushforward_congr _ _ h.symm _
  exact congrArg (fun c : AlgebraicCycle Y ℤ ↦ c (i w)) he

end AlgebraicGeometry.Scheme

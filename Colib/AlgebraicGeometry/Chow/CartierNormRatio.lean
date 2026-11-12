/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.CartierNormCycle
public import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport

/-!
# The principal cycle of the original norm ratio

The cross product of four actual affine equations identifies the full
Cartier cycle. Both the affine equations and the finite pushforward retain
the original multiplicities and residue degrees.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Chow Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme

/-- The affine norm ratios at every original point give the global
principal cycle of the same rational function. -/
theorem principalCycle_eq_cartierNormRatio
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f]
    (I₁ J₁ : X.IdealSheafData) (I₂ J₂ : Y.IdealSheafData)
    (hI₁ : IsEffectiveCartierDivisor I₁) (hJ₁ : IsEffectiveCartierDivisor J₁)
    (hI₂ : IsEffectiveCartierDivisor I₂) (hJ₂ : IsEffectiveCartierDivisor J₂)
    (r : Y.functionField) (hr : r ≠ 0)
    (hchart : ∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (hy : y ∈ U),
      letI : IsAffine U.toScheme := hU
      letI : Nonempty U := ⟨⟨y, hy⟩⟩
      letI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨y, hy⟩)
      letI : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨⟨y, hy⟩, trivial⟩⟩
      let f₀ := pullback.snd f U.ι
      letI : IsAffine (pullback f U.ι) := isAffine_of_isAffineHom f₀
      letI : Algebra Γ(U.toScheme, ⊤) Γ(pullback f U.ι, ⊤) := f₀.appTop.hom.toAlgebra
      ∃ (a₁ b₁ : Γ(pullback f U.ι, ⊤)) (a₂ b₂ : Γ(U.toScheme, ⊤)),
        Module.Free Γ(U.toScheme, ⊤) Γ(pullback f U.ι, ⊤) ∧
        (I₁.comap (pullback.fst f U.ι)).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {a₁} ∧
        (J₁.comap (pullback.fst f U.ι)).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {b₁} ∧
        (I₂.comap U.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {a₂} ∧
        (J₂.comap U.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {b₂} ∧
        dominantFunctionFieldMap U.ι r *
            U.toScheme.germToFunctionField ⊤ (Algebra.norm Γ(U.toScheme, ⊤) b₁) *
              U.toScheme.germToFunctionField ⊤ a₂ =
          U.toScheme.germToFunctionField ⊤ (Algebra.norm Γ(U.toScheme, ⊤) a₁) *
            U.toScheme.germToFunctionField ⊤ b₂) :
    principalCycle Y r =
      finiteCyclePushforward f (cartierCycle I₁ - cartierCycle J₁) -
        (cartierCycle I₂ - cartierCycle J₂) := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  obtain ⟨U, hU, hy, a₁, b₁, a₂, b₂, hfree, ha₁, hb₁, ha₂, hb₂, hprod⟩ := hchart y
  let : IsAffine U.toScheme := hU
  let : Nonempty U := ⟨⟨y, hy⟩⟩
  let : IsIntegral U.toScheme := inferInstance
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨y, hy⟩)
  let : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨⟨y, hy⟩, trivial⟩⟩
  let : IsNoetherian U.toScheme :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian U.ι
      toCompactSpace := inferInstance }
  let f₀ := pullback.snd f U.ι
  let i := pullback.fst f U.ι
  let : IsAffine (pullback f U.ι) := isAffine_of_isAffineHom f₀
  let : IsNoetherian (pullback f U.ι) :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian i
      toCompactSpace := inferInstance }
  let : Algebra Γ(U.toScheme, ⊤) Γ(pullback f U.ι, ⊤) := f₀.appTop.hom.toAlgebra
  let : Module.Free Γ(U.toScheme, ⊤) Γ(pullback f U.ι, ⊤) := hfree
  let z : U.toScheme := ⟨y, hy⟩
  let g := U.toScheme.germToFunctionField ⊤
  let r₀ := dominantFunctionFieldMap U.ι r
  have hI₁' := isPullbackDefined_of_flat i I₁ hI₁
  have hJ₁' := isPullbackDefined_of_flat i J₁ hJ₁
  have hI₂' := isPullbackDefined_of_flat U.ι I₂ hI₂
  have hJ₂' := isPullbackDefined_of_flat U.ι J₂ hJ₂
  have hreg₁ := Stacks.Divisors.Eta.mem_nonZeroDivisors_of_ideal_eq_span _ hI₁' _ ha₁
  have hreg₂ := Stacks.Divisors.Eta.mem_nonZeroDivisors_of_ideal_eq_span _ hJ₁' _ hb₁
  have hreg₃ := Stacks.Divisors.Eta.mem_nonZeroDivisors_of_ideal_eq_span _ hI₂' _ ha₂
  have hreg₄ := Stacks.Divisors.Eta.mem_nonZeroDivisors_of_ideal_eq_span _ hJ₂' _ hb₂
  let : IsDomain Γ(U.toScheme, ⊤) := IsIntegral.component_integral _
  let : Module.Finite Γ(U.toScheme, ⊤) Γ(pullback f U.ι, ⊤) := f₀.finite_appTop
  have hr₀ : r₀ ≠ 0 :=
    (map_ne_zero_iff _ (dominantFunctionFieldMap U.ι).injective).2 hr
  have hne {s : Γ(U.toScheme, ⊤)} (hs : s ≠ 0) : g s ≠ 0 :=
    (map_ne_zero_iff g.hom (U.toScheme.germToFunctionField_injective ⊤)).2 hs
  have hna := hne (Algebra.norm_ne_zero_of_isRegular a₁ (isRegular_iff_mem_nonZeroDivisors.2 hreg₁))
  have hnb := hne (Algebra.norm_ne_zero_of_isRegular b₁ (isRegular_iff_mem_nonZeroDivisors.2 hreg₂))
  have hta := hne (mem_nonZeroDivisors_iff_ne_zero.mp hreg₃)
  have htb := hne (mem_nonZeroDivisors_iff_ne_zero.mp hreg₄)
  have horder := congrArg (fun t ↦ U.toScheme.ord t z) hprod
  change U.toScheme.ord (r₀ * g (Algebra.norm Γ(U.toScheme, ⊤) b₁) * g a₂) z =
    U.toScheme.ord (g (Algebra.norm Γ(U.toScheme, ⊤) a₁) * g b₂) z at horder
  rw [U.toScheme.ord_mul (mul_ne_zero hr₀ hnb) hta, U.toScheme.ord_mul hr₀ hnb,
    U.toScheme.ord_mul hna htb] at horder
  have hSrcI := finiteCyclePushforward_apply_of_open_pullback f U
    (cartierCycle I₁) (cartierCycle (I₁.comap i))
    (cartierCycle_apply_of_isOpenImmersion I₁ hI₁ i) z
  have hSrcJ := finiteCyclePushforward_apply_of_open_pullback f U
    (cartierCycle J₁) (cartierCycle (J₁.comap i))
    (cartierCycle_apply_of_isOpenImmersion J₁ hJ₁ i) z
  have hTgtI := cartierCycle_apply_of_isOpenImmersion I₂ hI₂ U.ι z
  have hTgtJ := cartierCycle_apply_of_isOpenImmersion J₂ hJ₂ U.ι z
  have hrOrd : U.toScheme.ord r₀ z = Y.ord r y :=
    ord_dominantFunctionFieldMap_of_isOpenImmersion U.ι r z
  rw [principalCycle_apply, map_sub]
  change Y.ord r y =
    finiteCyclePushforward f (cartierCycle I₁) (U.ι z) -
      finiteCyclePushforward f (cartierCycle J₁) (U.ι z) -
      (cartierCycle I₂ (U.ι z) - cartierCycle J₂ (U.ι z))
  rw [← hrOrd, ← hSrcI, ← hSrcJ, ← hTgtI, ← hTgtJ,
    finiteCyclePushforward_cartierCycle_apply_affineNorm f₀ _ hI₁' a₁ ha₁ z,
    finiteCyclePushforward_cartierCycle_apply_affineNorm f₀ _ hJ₁' b₁ hb₁ z,
    cartierCycle_apply_affineSection _ hI₂' a₂ ha₂ z,
    cartierCycle_apply_affineSection _ hJ₂' b₂ hb₂ z]
  change U.toScheme.ord r₀ z =
    U.toScheme.ord (g (Algebra.norm Γ(U.toScheme, ⊤) a₁)) z -
      U.toScheme.ord (g (Algebra.norm Γ(U.toScheme, ⊤) b₁)) z -
      (U.toScheme.ord (g a₂) z - U.toScheme.ord (g b₂) z)
  omega

end AlgebraicGeometry.Scheme

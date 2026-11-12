/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass.WeilDivisorCycle
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionStalkLength
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.PrincipalDivisor

/-!
# Literal Weil divisors and whole Cartier fundamental cycles

The two pinned Stacks presentations of prime divisors are identified by their actual ideal
sheaves. Reindexing coefficients gives an additive comparison of their Weil groups, followed
by the existing native Chow cycle construction. For an effective Cartier divisor this cycle
is the finite pushforward of the fundamental cycle of its whole zero scheme. The comparison
uses the original stalk quotient, including its nilpotents, and not the reduced support.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Order

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The two pinned prime-divisor presentations have exactly the same ideal sheaf. -/
def PrimeDivisor.chowEquiv : PrimeDivisor X ≃ Stacks.Divisors.PrimeDivisor X where
  toFun Z := ⟨Z.idealSheaf, Z.integral, Z.codimension_one⟩
  invFun Z := ⟨Z.idealSheaf, Z.integral, Z.codimension_one⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem PrimeDivisor.chowEquiv_genericPoint (Z : PrimeDivisor X) :
    (PrimeDivisor.chowEquiv Z).genericPoint = Z.genericPoint := rfl

@[simp] theorem PrimeDivisor.chowEquiv_symm_genericPoint
    (Z : Stacks.Divisors.PrimeDivisor X) :
    (PrimeDivisor.chowEquiv.symm Z).genericPoint = Z.genericPoint := rfl

/-- Reindex the original signed coefficients without changing ideals or supports. -/
@[colib_tag "COL-1051"]
def WeilDivisor.chowEquiv : WeilDivisor X ≃+ Stacks.Divisors.WeilDivisor X where
  toFun D := ⟨fun Z => D.val (PrimeDivisor.chowEquiv.symm Z),
    D.property.comp_injective PrimeDivisor.chowEquiv.symm.injective⟩
  invFun D := ⟨fun Z => D.val (PrimeDivisor.chowEquiv Z),
    D.property.comp_injective PrimeDivisor.chowEquiv.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The existing native Chow cycle of the original Weil divisor, as an additive map. -/
def WeilDivisor.toAlgebraicCycle : WeilDivisor X →+ AlgebraicCycle X ℤ where
  toFun D := Stacks.Chow.weilDivisorAlgebraicCycle (WeilDivisor.chowEquiv D)
  map_zero' := by
    apply Function.locallyFinsuppWithin.ext
    intro x
    simp only [Stacks.Chow.weilDivisorAlgebraicCycle_apply, Stacks.Chow.weilDivisorCoeff]
    split_ifs <;> rfl
  map_add' D E := by
    apply Function.locallyFinsuppWithin.ext
    intro x
    simp only [Stacks.Chow.weilDivisorAlgebraicCycle_apply,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply, Stacks.Chow.weilDivisorCoeff]
    split_ifs <;> rfl

/-- At an original prime divisor the coefficient is unchanged. -/
@[simp] theorem WeilDivisor.toAlgebraicCycle_genericPoint (D : WeilDivisor X)
    (Z : PrimeDivisor X) : WeilDivisor.toAlgebraicCycle D Z.genericPoint = D.val Z := by
  exact Stacks.Chow.weilDivisorCoeff_genericPoint
    (WeilDivisor.chowEquiv D).val (PrimeDivisor.chowEquiv Z)

/-- Outside codimension one there is no divisor coefficient. -/
theorem WeilDivisor.toAlgebraicCycle_eq_zero_of_coheight_ne_one (D : WeilDivisor X)
    (x : X) (hx : coheight x ≠ 1) : WeilDivisor.toAlgebraicCycle D x = 0 :=
  Stacks.Chow.weilDivisorCoeff_eq_zero_of_coheight_ne_one _ hx

/-- The principal Weil divisor becomes the native principal cycle of the same rational unit. -/
theorem WeilDivisor.toAlgebraicCycle_principalDivisor [IsIntegral X]
    [IsLocallyNoetherian X] (f : (Stacks.Chow.rationalFunctions X)ˣ) :
    WeilDivisor.toAlgebraicCycle (principalDivisor X f) =
      Stacks.Chow.principalCycle X ((Stacks.Chow.rationalFunctionsEquivFunctionField X).val f) := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : coheight x = 1
  · obtain ⟨Z, rfl⟩ : ∃ Z : PrimeDivisor X, Z.genericPoint = x :=
      ⟨PrimeDivisor.ofCoheightOne x hx, PrimeDivisor.genericPoint_ofCoheightOne x hx⟩
    rw [WeilDivisor.toAlgebraicCycle_genericPoint]
    rfl
  · rw [WeilDivisor.toAlgebraicCycle_eq_zero_of_coheight_ne_one _ x hx]
    exact (Scheme.ord_eq_zero_of_coheight_neq_one hx _).symm

end AlgebraicGeometry

namespace Stacks.Chow

variable {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]

local instance subschemeNoetherian (I : X.IdealSheafData) : IsNoetherian I.subscheme :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace I.subschemeι }

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsIntegral X] in
/-- The original Cartier stalk quotient is the actual self-length of the zero-scheme stalk. -/
theorem effectiveCartierMultiplicity_eq_stalk_length (I : X.IdealSheafData)
    (Z : AlgebraicGeometry.PrimeDivisor X) (x : I.subscheme)
    (hx : I.subschemeι x = Z.genericPoint) :
    effectiveCartierMultiplicity I Z =
      ((Module.length (I.subscheme.presheaf.stalk x)
        (I.subscheme.presheaf.stalk x)).toNat : ℤ) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (I.subschemeι x))
  have h := length_stalk_self_eq_length_quotient_stalk_ker I.subschemeι x U hU hxU
  rw [Scheme.IdealSheafData.ker_subschemeι, hx] at h
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) h.symm

/-- The native cycle of an effective Cartier divisor is the pushed fundamental cycle of its
whole closed scheme. This comparison retains all generic stalk lengths. -/
@[colib_tag "COL-1051",
  stacks 02AR "Whole Cartier stalk-quotient lengths in the native cycle group"]
theorem toAlgebraicCycle_effectiveCartierWeilDivisor (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    AlgebraicGeometry.WeilDivisor.toAlgebraicCycle (effectiveCartierWeilDivisor I hI) =
      finiteCyclePushforward I.subschemeι (AlgebraicCycle.fundamentalCycle I.subscheme) := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x ∈ Set.range I.subschemeι
  · obtain ⟨d, rfl⟩ := hx
    rw [finiteCyclePushforward_apply_of_isClosedImmersion]
    by_cases hc : coheight (I.subschemeι d) = 1
    · let Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (I.subschemeι d) hc
      have hZ : Z.genericPoint = I.subschemeι d :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      rw [← hZ, AlgebraicGeometry.WeilDivisor.toAlgebraicCycle_genericPoint,
        effectiveCartierWeilDivisor_apply,
        effectiveCartierMultiplicity_eq_stalk_length I Z d hZ.symm]
      by_cases hd : d ∈ genericPoints I.subscheme
      · exact (AlgebraicCycle.fundamentalCycle_apply_generic I.subscheme ⟨d, hd⟩).symm
      · have htop : Module.length (I.subscheme.presheaf.stalk d)
            (I.subscheme.presheaf.stalk d) = ⊤ := by
          by_contra h
          exact hd ((length_stalk_ne_top_iff_mem_genericPoints d).mp h)
        rw [htop, ENat.toNat_top, Nat.cast_zero,
          AlgebraicCycle.fundamentalCycle_apply_of_notMem I.subscheme d hd]
    · rw [AlgebraicGeometry.WeilDivisor.toAlgebraicCycle_eq_zero_of_coheight_ne_one _ _ hc]
      apply (AlgebraicCycle.fundamentalCycle_apply_of_notMem I.subscheme d _).symm
      intro hd
      have hdim := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor I hI d
        ⟨⟨closure ({d} : Set I.subscheme), hd⟩, rfl⟩
      apply hc
      rw [ringKrullDim_stalk_eq_coheight] at hdim
      exact WithBot.coe_injective hdim
  · have hzero : finiteCyclePushforward I.subschemeι
        (AlgebraicCycle.fundamentalCycle I.subscheme) x = 0 := by
      by_contra h
      obtain ⟨d, -, hd⟩ := finiteCyclePushforward_support_subset I.subschemeι
        (AlgebraicCycle.fundamentalCycle I.subscheme) h
      exact hx ⟨d, hd⟩
    rw [hzero]
    by_cases hc : coheight x = 1
    · let Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hc
      have hZ : Z.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      rw [← hZ, AlgebraicGeometry.WeilDivisor.toAlgebraicCycle_genericPoint]
      apply effectiveCartierWeilDivisor_apply_of_notMem_support
      rw [hZ]
      change x ∉ (I.support : Set X)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact hx
    · exact AlgebraicGeometry.WeilDivisor.toAlgebraicCycle_eq_zero_of_coheight_ne_one _ _ hc

end Stacks.Chow

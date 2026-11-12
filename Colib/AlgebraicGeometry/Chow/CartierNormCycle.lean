/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.CartierCycle
public import Colib.AlgebraicGeometry.Chow.PrincipalSection
public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.FibreLength
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingDvrHilbert
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedBerthelotOgus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.GenericPointCoheight
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteFibre

/-!
# The full Cartier cycle of a norm on an affine chart

The actual finite pushforward of a Cartier zero scheme has the order of its
determinant norm. This identifies each coefficient with the full quotient
length and the actual residue degree, including disconnected finite sources.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Order Stacks.Chow Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme

/-- On an integral affine chart the original Cartier equation gives the
same principal order. -/
theorem cartierCycle_apply_affineSection {X : Scheme.{u}} [IsAffine X]
    [IsNoetherian X] [IsIntegral X] (I : X.IdealSheafData) (hI : IsEffectiveCartierDivisor I)
    (s : Γ(X, ⊤)) (hEq : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {s})
    (x : X) :
    letI : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    cartierCycle I x = X.ord (X.germToFunctionField ⊤ s) x := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  let : IsDomain Γ(X, ⊤) := IsIntegral.component_integral _
  have hs := Stacks.Divisors.Eta.mem_nonZeroDivisors_of_ideal_eq_span I hI
    ⟨⊤, isAffineOpen_top X⟩ hEq
  by_cases hx : coheight x = 1
  · rw [cartierCycle_apply_coheight_one I hI _ hx,
      ord_germ_eq_quotient_length ⊤ s (mem_nonZeroDivisors_iff_ne_zero.mp hs) trivial hx,
      IdealSheafData.stalk_eq_map_germ I x ⟨⊤, isAffineOpen_top X⟩ trivial, hEq,
      Ideal.map_span, Set.image_singleton]
  · rw [cartierCycle_apply_coheight_ne_one I hI _ hx, Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- Finite flat maps preserve the coheight of every actual point. -/
theorem coheight_eq_of_finite_flat {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [IsFinite f] [Flat f] (x : X) : coheight x = coheight (f x) := by
  let : DiscreteTopology (f.fiber (f x)) :=
    discreteTopology_fiber_of_finite_preimage f (f x) (f.finite_preimage_singleton (f x))
  exact coheight_eq_coheight_base_of_asFiber_mem_genericPoints f
    (mem_genericPoints_of_discreteTopology (f.asFiber x))

/-- The norm of the original affine equation computes the pushforward of
its whole Cartier zero cycle. -/
theorem finiteCyclePushforward_cartierCycle_apply_affineNorm {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsNoetherian X] [IsNoetherian Y] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I) (s : Γ(X, ⊤))
    (hEq : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {s}) (y : Y) :
    letI : Nonempty (⊤ : Y.Opens) := ⟨⟨y, trivial⟩⟩
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∀ [Module.Free Γ(Y, ⊤) Γ(X, ⊤)],
      finiteCyclePushforward f (cartierCycle I) y =
        Y.ord (Y.germToFunctionField ⊤ (Algebra.norm Γ(Y, ⊤) s)) y := by
  classical
  dsimp only
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨y, trivial⟩⟩
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : IsDomain Γ(Y, ⊤) := IsIntegral.component_integral _
  let : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  intro hfree
  let : Module.Free Γ(Y, ⊤) Γ(X, ⊤) := hfree
  have hs : _root_.IsRegular s := isRegular_iff_mem_nonZeroDivisors.2
    (Stacks.Divisors.Eta.mem_nonZeroDivisors_of_ideal_eq_span I hI
      ⟨⊤, isAffineOpen_top X⟩ hEq)
  let D : Set X := f.base ⁻¹' {y}
  let : Fintype D := (f.finite_preimage_singleton y).fintype
  have hcoh (x : D) : coheight (x : X) = coheight y :=
    (coheight_eq_of_finite_flat f x.val).trans (congrArg coheight x.property)
  have hstalk (x : X) : IdealSheafData.stalk I x =
      Ideal.span {X.presheaf.germ ⊤ x trivial s} := by
    rw [IdealSheafData.stalk_eq_map_germ I x ⟨⊤, isAffineOpen_top X⟩ trivial, hEq,
      Ideal.map_span, Set.image_singleton]
  rw [finiteCyclePushforward_apply]
  change (∑ᶠ x ∈ D, cartierCycle I x * (f.residueDegree x : ℤ)) = _
  rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  by_cases hy : coheight y = 1
  · rw [ord_germ_eq_quotient_length ⊤ _ (Algebra.norm_ne_zero_of_isRegular s hs) trivial hy,
      stalkQuotientLength_norm_eq_finsum_fibre f y hy s hs]
    change _ = (((∑ᶠ x ∈ D, (f.residueDegree x : ℕ∞) *
      Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ ⊤ x trivial s}))).toNat : ℤ)
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype, ENat.toNat_sum]
    · push_cast
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [cartierCycle_apply_coheight_one I hI x.val ((hcoh x).trans hy), hstalk,
        ENat.toNat_mul]
      simp only [ENat.toNat_natCast, Nat.cast_mul, mul_comm]
    · intro x _
      let : Ring.KrullDimLE 1 (X.presheaf.stalk x.val) :=
        krullDimLE_of_coheight_le ((hcoh x).trans hy).le
      have hreg := isRegular_germ ⟨⊤, isAffineOpen_top X⟩ x.val trivial hs
      exact WithTop.mul_ne_top (ENat.natCast_ne_top (f.residueDegree x.val))
        (Module.length_ne_top_iff.mpr
          (isFiniteLength_quotient_span_singleton
            (X.presheaf.stalk x.val) hreg.mem_nonZeroDivisors))
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hy]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    rw [cartierCycle_apply_coheight_ne_one I hI x.val (fun hx ↦ hy ((hcoh x).symm.trans hx)),
      zero_mul]

end AlgebraicGeometry.Scheme

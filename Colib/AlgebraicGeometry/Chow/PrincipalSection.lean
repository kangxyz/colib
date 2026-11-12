/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointCycle
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle

/-! # A regular section and the original principal order

The affine-line map retains the original global section. At a
codimension-one point its zero equation has the quotient length that
computes the native order.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Divisors/Order/PrincipalOrderCancellation.lean`
and the principal-section cycle and polynomial-family divisor maps in Motivic
at `a6805c4a87cdfd7717dd7a94039246a167f15380`. The genericity comparison
uses the native Krull dimensions of the original quotient stalks.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Order
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme

open AffineLineFiber

/-- The literal polynomial coordinate determined by a global section. -/
def sectionToAffineLine {R : Type u} [CommRing R] {P : Scheme.{u}}
    (p : P ⟶ Spec (.of R)) (s : Γ(P, ⊤)) : P ⟶ Spec (.of R[X]) :=
  ΓSpec.adjunction.homEquiv P (op (.of R[X]))
    (CommRingCat.ofHom (Polynomial.eval₂RingHom
      (p.appTop.hom.comp (ΓSpecIso (.of R)).inv.hom) s)).op

/-- Pullback of the actual polynomial coordinate is the original section. -/
theorem sectionToAffineLine_coordinate {R : Type u} [CommRing R] {P : Scheme.{u}}
    (p : P ⟶ Spec (.of R)) (s : Γ(P, ⊤)) :
    (sectionToAffineLine p s).appTop ((ΓSpecIso (.of R[X])).inv Polynomial.X) = s := by
  have h := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
    (CommRingCat.ofHom (Polynomial.eval₂RingHom
      (p.appTop.hom.comp (ΓSpecIso (.of R)).inv.hom) s))
  have he := congrArg (fun f => f Polynomial.X) h
  change (sectionToAffineLine p s).appTop ((ΓSpecIso (.of R[X])).inv Polynomial.X) =
    Polynomial.eval₂ (p.appTop.hom.comp (ΓSpecIso (.of R)).inv.hom) s Polynomial.X at he
  simpa only [Polynomial.eval₂_X] using he

/-- The zero scalar of the section map is its actual germ. -/
theorem sectionToAffineLine_zero_scalar {k : Type u} [Field k] {P : Scheme.{u}}
    (p : P ⟶ Spec (.of k)) (s : Γ(P, ⊤)) (x : P) :
    scalar (sectionToAffineLine p s) 0 x = P.presheaf.germ ⊤ x (by trivial) s := by
  simp only [scalar, pointScalar, map_zero, sub_zero]
  change (sectionToAffineLine p s).stalkMap x
      ((Spec (.of k[X])).presheaf.germ ⊤ ((sectionToAffineLine p s) x)
        (TopologicalSpace.Opens.mem_top _) ((ΓSpecIso (.of k[X])).inv Polynomial.X)) = _
  exact ((sectionToAffineLine p s).germ_stalkMap_apply ⊤ x
    (TopologicalSpace.Opens.mem_top _) ((ΓSpecIso (.of k[X])).inv Polynomial.X)).trans
    (congrArg (P.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x))
      (sectionToAffineLine_coordinate p s))

/-- The native order of a nonzero local equation is the length of its
original principal quotient in the codimension-one stalk. -/
theorem ord_germ_eq_quotient_length {P : Scheme.{u}} [IsIntegral P] [IsLocallyNoetherian P]
    (U : P.Opens) [Nonempty U] (r : Γ(P, U)) (hr : r ≠ 0)
    {x : P} (hxU : x ∈ U) (hx : coheight x = 1) :
    P.ord (P.germToFunctionField U r) x =
      ((Module.length (P.presheaf.stalk x)
        ((P.presheaf.stalk x) ⧸ Ideal.span {P.presheaf.germ U x hxU r})).toNat : ℤ) := by
  let : Ring.KrullDimLE 1 (P.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hg : P.presheaf.germ U x hxU r ≠ 0 :=
    (map_ne_zero_iff (P.presheaf.germ U x hxU).hom
      (germ_injective_of_isIntegral P x hxU)).mpr hr
  have hf : P.germToFunctionField U r ≠ 0 :=
    (map_ne_zero_iff (P.germToFunctionField U).hom
      (P.germToFunctionField_injective U)).mpr hr
  apply (P.ord_eq_iff hx hf).mpr
  change Ring.ordFrac (P.presheaf.stalk x) (P.germToFunctionField U r) = _
  rw [← P.algebraMap_germ_eq_germToFunctionField hxU r, Ring.ordFrac_eq_ord _ hg]
  apply Ring.ordMonoidWithZeroHom_eq_coe (P.presheaf.stalk x)
    (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
  exact (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hg))).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

open AffineLineFiber Stacks.Chow
open Function.locallyFinsuppWithin

variable {k : Type u} [Field k] {P : Scheme.{u}} [IsIntegral P] [IsNoetherian P]
  (p : P ⟶ Spec (.of k)) (s : Γ(P, ⊤)) (hs : s ≠ 0)

local notation "f" => sectionToAffineLine p s
local notation "Z" => fiber f 0
local notation "i" => inclusion f 0

omit [IsNoetherian P] in
include hs in
private theorem section_zero_scalar_ne_zero (x : P) : scalar f 0 x ≠ 0 := by
  rw [sectionToAffineLine_zero_scalar]
  exact (map_ne_zero_iff (P.presheaf.germ ⊤ x (by trivial)).hom
    (germ_injective_of_isIntegral P x (by trivial))).mpr hs

include hs in
/-- A generic point of the literal zero scheme has ambient coheight one. -/
theorem section_zero_generic_coheight (y : Z) (hy : y ∈ genericPoints Z) :
    coheight (i y) = 1 := by
  have hzero : ringKrullDim (P.presheaf.stalk (i y) ⧸ Ideal.span {scalar f 0 (i y)}) = 0 :=
    (ringKrullDim_eq_of_ringEquiv (stalkQuotientEquiv f 0 y)).trans
      ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints Z y).mpr hy)
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (IsSMulRegular.of_ne_zero (section_zero_scalar_ne_zero p s hs (i y)))
    (scalar_mem_maximalIdeal f 0 y)
  rw [hzero, zero_add, ringKrullDim_stalk_eq_coheight] at hdim
  exact_mod_cast hdim.symm

include hs in
/-- A point of the literal zero scheme over a coheight-one point is generic. -/
theorem section_zero_generic_of_coheight (y : Z) (hy : coheight (i y) = 1) :
    y ∈ genericPoints Z := by
  let : Ring.KrullDimLE 1 (P.presheaf.stalk (i y)) := krullDimLE_of_coheight_le hy.le
  let r := scalar f 0 (i y)
  have hlen := isFiniteLength_quotient_span_singleton (P.presheaf.stalk (i y))
    (mem_nonZeroDivisors_iff_ne_zero.mpr (section_zero_scalar_ne_zero p s hs (i y)))
  have : IsArtinian (P.presheaf.stalk (i y)) (P.presheaf.stalk (i y) ⧸ Ideal.span {r}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  have : IsArtinianRing (P.presheaf.stalk (i y) ⧸ Ideal.span {r}) :=
    isArtinian_of_tower (P.presheaf.stalk (i y)) inferInstance
  have : IsArtinianRing ((fiber f 0).presheaf.stalk y) := (stalkQuotientEquiv f 0 y).isArtinianRing
  have : Ring.KrullDimLE 0 ((fiber f 0).presheaf.stalk y) :=
    isArtinianRing_iff_krullDimLE_zero.mp inferInstance
  exact (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints Z y).mp
    (ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance)

omit [IsNoetherian P] in
/-- The actual germ in the function field of the global equation. -/
def sectionRationalFunction : P.functionField :=
  letI : Nonempty (⊤ : P.Opens) := ⟨⟨genericPoint P, by trivial⟩⟩
  P.germToFunctionField ⊤ s

/-- The whole unreduced zero scheme, pushed to the original native cycle group. -/
def sectionZeroCycle : AlgebraicCycle P ℤ :=
  finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle Z)

include hs in
/-- The whole zero scheme has the native principal order, with its actual quotient lengths. -/
theorem sectionZeroCycle_eq_principalCycle :
    sectionZeroCycle p s = principalCycle P (sectionRationalFunction s) := by
  let : Nonempty (⊤ : P.Opens) := ⟨⟨genericPoint P, by trivial⟩⟩
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [sectionZeroCycle, principalCycle_apply, sectionRationalFunction]
  by_cases hx : coheight x = 1
  · rw [AlgebraicCycle.fundamentalCycle_pushforward_closed_apply _ _ (by
      intro y hy
      exact section_zero_generic_of_coheight p s hs y (hy.symm ▸ hx)),
      closedImmersionQuotientStalkLength, inclusion_stalk, sectionToAffineLine_zero_scalar,
      ord_germ_eq_quotient_length ⊤ s hs (by trivial) hx]
  · rw [AlgebraicCycle.fundamentalCycle_pushforward_closed_eq_zero _ _ (by
      intro y hy hg
      exact hx (hy ▸ section_zero_generic_coheight p s hs y hg)),
      Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- Signed zero schemes compute the divisor of the actual fraction. -/
theorem sectionZeroCycle_sub_eq_principalCycle (n d : Γ(P, ⊤)) (hn : n ≠ 0) (hd : d ≠ 0) :
    sectionZeroCycle p n - sectionZeroCycle p d =
      principalCycle P (sectionRationalFunction n / sectionRationalFunction d) := by
  let : Nonempty (⊤ : P.Opens) := ⟨⟨genericPoint P, by trivial⟩⟩
  have hn' : sectionRationalFunction n ≠ 0 :=
    (map_ne_zero_iff _ (P.germToFunctionField_injective ⊤)).mpr hn
  have hd' : sectionRationalFunction d ≠ 0 :=
    (map_ne_zero_iff _ (P.germToFunctionField_injective ⊤)).mpr hd
  have h := principalCycle_mul P (div_ne_zero hn' hd') hd'
  rw [div_mul_cancel₀ _ hd'] at h
  rw [sectionZeroCycle_eq_principalCycle p n hn, sectionZeroCycle_eq_principalCycle p d hd,
    h, add_sub_cancel_right]

end AlgebraicGeometry.Scheme

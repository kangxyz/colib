/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Multiplicity.PrincipalEuler.Support
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Principal Euler lengths of two successive cuts

For two scalars that are each regular on a module, the scalar homology of
the two successive cuts is symmetric in the scalars. The common cokernel
is the quotient by the sum of their images. The common kernel comes from
pairs `(x, y)` satisfying `b • x = a • y`. Both projections to the
respective kernels are surjective and identify the same pairs with zero.
-/

public noncomputable section

namespace Module

universe u v

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

open LinearMap Submodule

private abbrev scalarRelation (a b : A) : Submodule A (M × M) :=
  ker ((lsmul A M b).comp (LinearMap.fst A M M) - (lsmul A M a).comp (LinearMap.snd A M M))

private theorem scalarRelation_eq (a b : A) (z : scalarRelation (M := M) a b) :
    b • z.val.1 = a • z.val.2 :=
  sub_eq_zero.mp z.property

private def scalarRelationLeft (a b : A) :
    scalarRelation (M := M) a b →ₗ[A] ker (lsmul A (M ⧸ range (lsmul A M a)) b) :=
  ((range (lsmul A M a)).mkQ.comp
    ((LinearMap.fst A M M).comp (scalarRelation a b).subtype)).codRestrict _ fun z => by
      change b • (range (lsmul A M a)).mkQ z.val.1 = 0
      rw [← map_smul, scalarRelation_eq a b z, mkQ_apply, Quotient.mk_eq_zero]
      exact mem_range_self (lsmul A M a) z.val.2

private def scalarRelationRight (a b : A) :
    scalarRelation (M := M) a b →ₗ[A] ker (lsmul A (M ⧸ range (lsmul A M b)) a) :=
  ((range (lsmul A M b)).mkQ.comp
    ((LinearMap.snd A M M).comp (scalarRelation a b).subtype)).codRestrict _ fun z => by
      change a • (range (lsmul A M b)).mkQ z.val.2 = 0
      rw [← map_smul, ← scalarRelation_eq a b z, mkQ_apply, Quotient.mk_eq_zero]
      exact mem_range_self (lsmul A M b) z.val.1

/-- The actual scalar kernels of the two orders of cutting by regular scalars
are linearly equivalent. Each class is sent to the other coordinate of a pair
satisfying `b • x = a • y`. -/
def principalKernelEquivSwap (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b) :
    ker (lsmul A (M ⧸ range (lsmul A M a)) b) ≃ₗ[A]
      ker (lsmul A (M ⧸ range (lsmul A M b)) a) := by
  let left := scalarRelationLeft (M := M) a b
  let right := scalarRelationRight (M := M) a b
  have hleft : Function.Surjective left := by
    intro z
    obtain ⟨x, hx⟩ := mkQ_surjective (range (lsmul A M a)) z.val
    have h : b • x ∈ range (lsmul A M a) := by
      apply (Quotient.mk_eq_zero _).mp
      rw [← mkQ_apply, map_smul, hx]
      exact z.property
    obtain ⟨y, hy⟩ := h
    exact ⟨⟨(x, y), sub_eq_zero.mpr hy.symm⟩, Subtype.ext hx⟩
  have hright : Function.Surjective right := by
    intro z
    obtain ⟨y, hy⟩ := mkQ_surjective (range (lsmul A M b)) z.val
    have h : a • y ∈ range (lsmul A M b) := by
      apply (Quotient.mk_eq_zero _).mp
      rw [← mkQ_apply, map_smul, hy]
      exact z.property
    obtain ⟨x, hx⟩ := h
    exact ⟨⟨(x, y), sub_eq_zero.mpr hx⟩, Subtype.ext hy⟩
  have hker : ker left = ker right := by
    ext z
    change left z = 0 ↔ right z = 0
    have hx : left z = 0 ↔ z.val.1 ∈ range (lsmul A M a) := by
      constructor
      · intro h
        exact (Quotient.mk_eq_zero _).mp (congrArg Subtype.val h)
      · intro h
        exact Subtype.ext ((Quotient.mk_eq_zero _).mpr h)
    have hy : right z = 0 ↔ z.val.2 ∈ range (lsmul A M b) := by
      constructor
      · intro h
        exact (Quotient.mk_eq_zero _).mp (congrArg Subtype.val h)
      · intro h
        exact Subtype.ext ((Quotient.mk_eq_zero _).mpr h)
    rw [hx, hy]
    constructor
    · rintro ⟨w, hw⟩
      change a • w = z.val.1 at hw
      refine ⟨w, ha ?_⟩
      change a • (b • w) = a • z.val.2
      rw [smul_comm a b w, hw, scalarRelation_eq a b z]
    · rintro ⟨w, hw⟩
      change b • w = z.val.2 at hw
      refine ⟨w, hb ?_⟩
      change b • (a • w) = b • z.val.1
      rw [smul_comm b a w, hw, scalarRelation_eq a b z]
  exact (left.quotKerEquivOfSurjective hleft).symm.trans
    ((quotEquivOfEq _ _ hker).trans (right.quotKerEquivOfSurjective hright))

private theorem range_lsmul_quotient (S : Submodule A M) (b : A) :
    range (lsmul A (M ⧸ S) b) = (range (lsmul A M b)).map S.mkQ := by
  rw [← range_comp]
  have h : S.mkQ.comp (lsmul A M b) = (lsmul A (M ⧸ S) b).comp S.mkQ :=
    LinearMap.ext fun x => map_smul S.mkQ b x
  rw [h, range_comp_of_range_eq_top _ (range_mkQ S)]

/-- The scalar cokernel after two cuts is the quotient by the sum of the
two scalar images in the original module. -/
def principalCokernelEquivQuotientSup (a b : A) :
    ((M ⧸ range (lsmul A M a)) ⧸ range (lsmul A (M ⧸ range (lsmul A M a)) b)) ≃ₗ[A]
      (M ⧸ range (lsmul A M a) ⊔ range (lsmul A M b)) :=
  (quotEquivOfEq _ _ (range_lsmul_quotient _ b)).trans (quotientQuotientEquivQuotientSup _ _)

/-- The Euler length is symmetric in two scalars that are separately regular
on the original module. The two second scalar maps may have nonzero kernels. -/
theorem principalEuler_quotient_range_lsmul_comm (a b : A)
    (ha : IsSMulRegular M a) (hb : IsSMulRegular M b) :
    principalEuler (N := M ⧸ range (lsmul A M a)) b =
      principalEuler (N := M ⧸ range (lsmul A M b)) a := by
  rw [principalEuler_eq_length_quotient_sub_length_ker,
    principalEuler_eq_length_quotient_sub_length_ker,
    (principalCokernelEquivQuotientSup (M := M) a b).length_eq,
    (principalCokernelEquivQuotientSup (M := M) b a).length_eq,
    sup_comm (range (lsmul A M a)) (range (lsmul A M b)),
    (principalKernelEquivSwap (M := M) a b ha hb).length_eq]

private theorem range_lsmul_self (a : A) :
    range (lsmul A A a) = (Ideal.span {a} : Submodule A A) := by
  change range (lsmul A A a) = Submodule.span A {a}
  rw [LinearMap.span_singleton_eq_range]
  apply congrArg LinearMap.range
  apply LinearMap.ext
  intro x
  exact mul_comm a x

/-- In a ring, the two orders of cutting by principal ideals give equal Euler
lengths when the scalars are separately regular on the ring. -/
theorem principalEuler_quotient_span_singleton_comm (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular A b) :
    principalEuler (N := A ⧸ Ideal.span {a}) b =
      principalEuler (N := A ⧸ Ideal.span {b}) a := by
  rw [← range_lsmul_self a, ← range_lsmul_self b]
  exact principalEuler_quotient_range_lsmul_comm a b ha hb

/-- Finite length of the common cokernel gives finite scalar homology for
both orders of cutting a finite module over a Noetherian ring. -/
theorem finitePrincipal_quotient_range_lsmul [IsNoetherianRing A] [Module.Finite A M]
    (a b : A) (h : Module.length A (M ⧸ range (lsmul A M a) ⊔ range (lsmul A M b)) ≠ ⊤) :
    FinitePrincipal (M ⧸ range (lsmul A M a)) b ∧
      FinitePrincipal (M ⧸ range (lsmul A M b)) a := by
  constructor
  · apply finitePrincipal_of_finite_cokernel
    rw [(principalCokernelEquivQuotientSup (M := M) a b).length_eq]
    exact h
  · apply finitePrincipal_of_finite_cokernel
    rw [(principalCokernelEquivQuotientSup (M := M) b a).length_eq,
      sup_comm (range (lsmul A M b)) (range (lsmul A M a))]
    exact h

end Module

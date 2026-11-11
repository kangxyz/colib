/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenEquivarianceAcross
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTowerSeparable
public import Mathlib.Algebra.Field.ULift

/-!
# Finite Milnor norms across independent universes

Apply the native chosen norm to the two fields in their common universe, and
transport back along the canonical lift equivalences. For a separable tower,
simultaneous equivariance compares the three pairwise norms to the native norms
in one common universe. All endpoints use the original Milnor rings and groups.
-/

public noncomputable section

universe u v w a b c

namespace Stacks.Chow

private abbrev liftAlgebra (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] :
    Algebra (ULift.{a} k) (ULift.{b} L) :=
  ULift.algebra' k (ULift.{b} L)

attribute [local instance] liftAlgebra

private theorem liftAlgebra_commutes (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L] :
    (ULift.ringEquiv : ULift.{b} L ≃+* L).symm.toRingHom.comp (algebraMap k L) =
      (algebraMap (ULift.{a} k) (ULift.{b} L)).comp
        (ULift.ringEquiv : ULift.{a} k ≃+* k).symm.toRingHom :=
  RingHom.ext fun _ => rfl

private theorem liftFinite (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] : FiniteDimensional (ULift.{a} k) (ULift.{b} L) :=
  Module.Finite.of_equiv_equiv ULift.ringEquiv.symm ULift.ringEquiv.symm
    (liftAlgebra_commutes k L).symm

attribute [local instance] liftFinite

private theorem liftSeparable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] : Algebra.IsSeparable (ULift.{a} k) (ULift.{b} L) := by
  constructor
  intro x
  change (minpoly (ULift.{a} k) x).Separable
  have h : (minpoly k x.down).map (ULift.ringEquiv : ULift.{a} k ≃+* k).symm.toRingHom =
      minpoly (ULift.{a} k) x :=
    minpoly.map_eq_of_equiv_equiv
      (f := (ULift.ringEquiv : ULift.{a} k ≃+* k).symm)
      (g := (ULift.ringEquiv : ULift.{b} L ≃+* L).symm)
      (liftAlgebra_commutes k L).symm x.down
  rw [← h]
  exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable k x.down)

attribute [local instance] liftSeparable

private theorem liftScalarTower (k : Type u) (M : Type v) (L : Type w)
    [Field k] [Field M] [Field L] [Algebra k M] [Algebra M L] [Algebra k L]
    [IsScalarTower k M L] :
    IsScalarTower (ULift.{a} k) (ULift.{b} M) (ULift.{c} L) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    congrArg ULift.up (IsScalarTower.algebraMap_apply k M L x.down)

private theorem milnorKRingMapLift_symm_apply
    {k : Type u} {L : Type v} [Field k] [Field L]
    (e : k ≃+* L) (x : MilnorKRing k) :
    milnorKRingMapLift e.symm.toRingHom (milnorKRingMapLift e.toRingHom x) = x := by
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id k := RingEquiv.symm_comp e
  rw [milnorKRingMapLift_comp_apply, he, milnorKRingMapLift_eq,
    milnorKRingMap_id_apply]

/-- The additive Milnor norm for a finite extension whose fields may lie in
independent universes, formed from the native chosen norm. -/
def milnorKNormRingAcross (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] : MilnorKRing L →+ MilnorKRing k :=
  (milnorKRingMapLift (ULift.ringEquiv : ULift.{max u v} k ≃+* k).toRingHom).toAddMonoidHom.comp
    ((milnorKNormRing (ULift.{max u v} k) (ULift.{max u v} L)).comp
      (milnorKRingMapLift
        (ULift.ringEquiv : ULift.{max u v} L ≃+* L).symm.toRingHom).toAddMonoidHom)

/-- The norm across independent universes preserves the native grading. -/
theorem milnorKNormRingAcross_mem_milnorKGrading
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    {n : ℕ} {x : MilnorKRing L} (hx : x ∈ milnorKGrading L n) :
    milnorKNormRingAcross k L x ∈ milnorKGrading k n := by
  let z := milnorKTheoryMap (ULift.ringEquiv : ULift.{max u v} k ≃+* k).toRingHom n
    (milnorKNorm (ULift.{max u v} k) (ULift.{max u v} L) n
      (milnorKTheoryMap (ULift.ringEquiv : ULift.{max u v} L ≃+* L).symm.toRingHom n ⟨x, hx⟩))
  have hz : (z : MilnorKRing k) = milnorKNormRingAcross k L x := by
    simp only [z, ← milnorKRingMapLift_coe, coe_milnorKNorm]
    rfl
  exact hz ▸ z.2

/-- The norm across independent universes on the native homogeneous Milnor group. -/
@[expose] def milnorKNormAcross (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] (n : ℕ) : MilnorKTheory L n →+ MilnorKTheory k n where
  toFun x := ⟨milnorKNormRingAcross k L x, milnorKNormRingAcross_mem_milnorKGrading x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The homogeneous norm is the restriction of the whole-ring norm. -/
@[simp] theorem coe_milnorKNormAcross
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    (n : ℕ) (x : MilnorKTheory L n) :
    (milnorKNormAcross k L n x : MilnorKRing k) = milnorKNormRingAcross k L x := rfl

/-- In a common universe the norm equals the original chosen norm for a finite
separable extension. -/
theorem milnorKNormRingAcross_eq_of_isSeparable
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    milnorKNormRingAcross k L = milnorKNormRing k L := by
  apply AddMonoidHom.ext
  intro x
  let σ : ULift.{u} k ≃+* k := ULift.ringEquiv
  let τ : ULift.{u} L ≃+* L := ULift.ringEquiv
  have hστ : τ.toRingHom.comp (algebraMap (ULift.{u} k) (ULift.{u} L)) =
      (algebraMap k L).comp σ.toRingHom := RingHom.ext fun _ => rfl
  have h := milnorKNormRing_map_ringEquiv_across_of_isSeparable σ τ hστ
    (milnorKRingMapLift τ.symm.toRingHom x)
  have hcancel := milnorKRingMapLift_symm_apply τ.symm x
  rw [RingEquiv.symm_symm] at hcancel
  rw [hcancel] at h
  exact h

/-- In each homogeneous degree the common-universe norm is the original chosen norm. -/
theorem milnorKNormAcross_eq_of_isSeparable
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] (n : ℕ) :
    milnorKNormAcross k L n = milnorKNorm k L n := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (milnorKNormRingAcross_eq_of_isSeparable k L) (x : MilnorKRing L)

/-- Compare the pairwise lift to a larger common lift. -/
private theorem milnorKNormRingAcross_eq_lift
    (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] (x : MilnorKRing L) :
    milnorKNormRingAcross k L x =
      milnorKRingMapLift (ULift.ringEquiv : ULift.{max u v w} k ≃+* k).toRingHom
        (milnorKNormRing (ULift.{max u v w} k) (ULift.{max u v w} L)
          (milnorKRingMapLift
            (ULift.ringEquiv : ULift.{max u v w} L ≃+* L).symm.toRingHom x)) := by
  let σ : ULift.{max u v} k ≃+* ULift.{max u v w} k :=
    ULift.ringEquiv.trans ULift.ringEquiv.symm
  let τ : ULift.{max u v} L ≃+* ULift.{max u v w} L :=
    ULift.ringEquiv.trans ULift.ringEquiv.symm
  have hστ : τ.toRingHom.comp (algebraMap (ULift.{max u v} k) (ULift.{max u v} L)) =
      (algebraMap (ULift.{max u v w} k) (ULift.{max u v w} L)).comp σ.toRingHom :=
    RingHom.ext fun _ => rfl
  have h := congrArg
    (milnorKRingMapLift (ULift.ringEquiv : ULift.{max u v w} k ≃+* k).toRingHom)
    (milnorKNormRing_map_ringEquiv_across_of_isSeparable σ τ hστ
      (milnorKRingMapLift (ULift.ringEquiv : ULift.{max u v} L ≃+* L).symm.toRingHom x))
  simp only [milnorKRingMapLift_comp_apply] at h
  exact h

/-- The norms compose in a finite separable tower with independent universes and
the original compatible algebra maps. -/
theorem milnorKNormRingAcross_tower_of_isSeparable
    {k : Type u} {M : Type v} {L : Type w} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (x : MilnorKRing L) :
    milnorKNormRingAcross k M (milnorKNormRingAcross M L x) = milnorKNormRingAcross k L x := by
  let : Algebra.IsSeparable k M := Algebra.isSeparable_tower_bot_of_isSeparable k M L
  let : Algebra.IsSeparable M L := Algebra.isSeparable_tower_top_of_isSeparable k M L
  let : IsScalarTower (ULift.{max u v w} k) (ULift.{max u v w} M) (ULift.{max u v w} L) :=
    liftScalarTower k M L
  rw [milnorKNormRingAcross_eq_lift.{v, w, u} M L,
    milnorKNormRingAcross_eq_lift.{u, v, w} k M, milnorKNormRingAcross_eq_lift.{u, w, v} k L,
    milnorKRingMapLift_symm_apply (ULift.ringEquiv : ULift.{max u v w} M ≃+* M),
    milnorKNormRing_tower_of_isSeparable]

/-- Tower transitivity as equality of whole-ring additive maps. -/
theorem milnorKNormRingAcross_comp_milnorKNormRingAcross_of_isSeparable
    {k : Type u} {M : Type v} {L : Type w} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] :
    (milnorKNormRingAcross k M).comp (milnorKNormRingAcross M L) = milnorKNormRingAcross k L := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNormRingAcross_tower_of_isSeparable x

/-- Tower transitivity on the native homogeneous Milnor group. -/
theorem milnorKNormAcross_tower_of_isSeparable
    {k : Type u} {M : Type v} {L : Type w} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L]
    (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNormAcross k M n (milnorKNormAcross M L n x) = milnorKNormAcross k L n x := by
  apply Subtype.ext
  exact milnorKNormRingAcross_tower_of_isSeparable (x : MilnorKRing L)

/-- Tower transitivity as equality of homogeneous additive maps. -/
theorem milnorKNormAcross_comp_milnorKNormAcross_of_isSeparable
    {k : Type u} {M : Type v} {L : Type w} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (n : ℕ) :
    @Eq (MilnorKTheory L n →+ MilnorKTheory k n)
      (AddMonoidHom.comp (M := MilnorKTheory L n) (N := MilnorKTheory M n)
        (P := MilnorKTheory k n) (milnorKNormAcross k M n) (milnorKNormAcross M L n))
      (milnorKNormAcross k L n) := by
  refine AddMonoidHom.ext (M := MilnorKTheory L n) (N := MilnorKTheory k n) ?_
  intro x
  exact milnorKNormAcross_tower_of_isSeparable (k := k) (M := M) (L := L) n x

attribute [colib_tag "COL-1021"]
  milnorKNormRingAcross milnorKNormAcross
  milnorKNormRingAcross_eq_of_isSeparable milnorKNormAcross_eq_of_isSeparable
  milnorKNormRingAcross_tower_of_isSeparable
  milnorKNormRingAcross_comp_milnorKNormRingAcross_of_isSeparable
  milnorKNormAcross_tower_of_isSeparable milnorKNormAcross_comp_milnorKNormAcross_of_isSeparable

end Stacks.Chow

end

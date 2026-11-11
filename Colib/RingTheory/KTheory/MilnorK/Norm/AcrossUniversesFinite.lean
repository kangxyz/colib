/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.AcrossUniverses
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenEquivarianceFiniteAcross

/-!
# Finite tower coherence across independent universes

Compare every pairwise norm in a common lift of the three original fields.
The two transports through the middle field cancel. The resulting identity
is the native finite tower law in the common universe.
-/

public noncomputable section

universe u v w

namespace Stacks.Chow

attribute [local instance] liftAlgebra liftFinite

/-- In a common universe the norm equals the original chosen norm for any finite
extension. -/
theorem milnorKNormRingAcross_eq_of_finite
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] :
    milnorKNormRingAcross k L = milnorKNormRing k L := by
  apply AddMonoidHom.ext
  intro x
  let σ : ULift.{u} k ≃+* k := ULift.ringEquiv
  let τ : ULift.{u} L ≃+* L := ULift.ringEquiv
  have hστ : τ.toRingHom.comp (algebraMap (ULift.{u} k) (ULift.{u} L)) =
      (algebraMap k L).comp σ.toRingHom := RingHom.ext fun _ => rfl
  have h := milnorKNormRing_map_ringEquiv_across_of_finite σ τ hστ
    (milnorKRingMapLift τ.symm.toRingHom x)
  have hcancel := milnorKRingMapLift_symm_apply τ.symm x
  rw [RingEquiv.symm_symm] at hcancel
  rw [hcancel] at h
  exact h

/-- In each homogeneous degree the common-universe norm is the original chosen norm. -/
theorem milnorKNormAcross_eq_of_finite
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] (n : ℕ) :
    milnorKNormAcross k L n = milnorKNorm k L n := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (milnorKNormRingAcross_eq_of_finite k L) (x : MilnorKRing L)

/-- Compare the pairwise lift to a larger common lift. -/
private theorem milnorKNormRingAcross_eq_lift
    (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] (x : MilnorKRing L) :
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
    (milnorKNormRing_map_ringEquiv_across_of_finite σ τ hστ
      (milnorKRingMapLift (ULift.ringEquiv : ULift.{max u v} L ≃+* L).symm.toRingHom x))
  simp only [milnorKRingMapLift_comp_apply] at h
  exact h

/-- The norms compose in a finite tower with independent universes and
the original compatible algebra maps. -/
theorem milnorKNormRingAcross_tower_of_finite
    {k : Type u} {M : Type v} {L : Type w} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (x : MilnorKRing L) :
    milnorKNormRingAcross k M (milnorKNormRingAcross M L x) = milnorKNormRingAcross k L x := by
  let : IsScalarTower (ULift.{max u v w} k) (ULift.{max u v w} M) (ULift.{max u v w} L) :=
    liftScalarTower k M L
  rw [milnorKNormRingAcross_eq_lift.{v, w, u} M L,
    milnorKNormRingAcross_eq_lift.{u, v, w} k M, milnorKNormRingAcross_eq_lift.{u, w, v} k L,
    milnorKRingMapLift_symm_apply (ULift.ringEquiv : ULift.{max u v w} M ≃+* M),
    milnorKNormRing_tower_of_finite]

/-- Tower transitivity as equality of whole-ring additive maps. -/
theorem milnorKNormRingAcross_comp_milnorKNormRingAcross_of_finite
    {k : Type u} {M : Type v} {L : Type w} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
     [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] :
    (milnorKNormRingAcross k M).comp (milnorKNormRingAcross M L) = milnorKNormRingAcross k L := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNormRingAcross_tower_of_finite x

/-- Tower transitivity on the native homogeneous Milnor group. -/
theorem milnorKNormAcross_tower_of_finite
    {k : Type u} {M : Type v} {L : Type w} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
     [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L]
    (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNormAcross k M n (milnorKNormAcross M L n x) = milnorKNormAcross k L n x := by
  apply Subtype.ext
  exact milnorKNormRingAcross_tower_of_finite (x : MilnorKRing L)

/-- Tower transitivity as equality of homogeneous additive maps. -/
theorem milnorKNormAcross_comp_milnorKNormAcross_of_finite
    {k : Type u} {M : Type v} {L : Type w} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
     [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (n : ℕ) :
    @Eq (MilnorKTheory L n →+ MilnorKTheory k n)
      (AddMonoidHom.comp (M := MilnorKTheory L n) (N := MilnorKTheory M n)
        (P := MilnorKTheory k n) (milnorKNormAcross k M n) (milnorKNormAcross M L n))
      (milnorKNormAcross k L n) := by
  refine AddMonoidHom.ext (M := MilnorKTheory L n) (N := MilnorKTheory k n) ?_
  intro x
  exact milnorKNormAcross_tower_of_finite (k := k) (M := M) (L := L) n x

attribute [colib_tag "COL-1027"]
  milnorKNormRingAcross_eq_of_finite milnorKNormAcross_eq_of_finite
  milnorKNormRingAcross_comp_milnorKNormRingAcross_of_finite
  milnorKNormRingAcross_tower_of_finite milnorKNormAcross_tower_of_finite

attribute [colib_tag "COL-1027",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/Chow/MilnorNorm/FieldNorm.lean:212-272" "ingredient"
    "The original finite recursion, whole-ring norm and homogeneous norm are the maps \
      compared in a common universe."]
  milnorKNormAcross_comp_milnorKNormAcross_of_finite

end Stacks.Chow

end

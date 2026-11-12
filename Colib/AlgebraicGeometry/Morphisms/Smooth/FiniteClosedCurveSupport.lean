/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import Colib.AlgebraicGeometry.Morphisms.Finite.ProperQuasiAffine

/-! # Finite closed supports in smooth relative curves

The generic point of a codimension-one closed support finite over the base
lies over an actual component generic point of the base.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Cycles/Divisors/CodimensionOneDominance.lean`
and `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Boundary/NeighborhoodComplement.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] specializationOrder

private theorem image_mem_genericPoints_of_coheight_one_closed_fiber
    {X S : Scheme.{u}} (q : X ⟶ S) [SmoothOfRelativeDimension 1 q]
    (x : X) (hx : coheight x = 1)
    (hc : IsClosed ({q.asFiber x} : Set (q.fiber (q x)))) :
    q x ∈ genericPoints S := by
  let : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  let y := q x
  let a := q.asFiber x
  let f := q.fiberToSpecResidueField y
  let : SmoothOfRelativeDimension 1 f :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback q (S.fromSpecResidueField y)) inferInstance
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have ha : coheight a = 1 := by
    have hdim := topologicalKrullDimAt_eq_one_of_smoothOfRelativeDimension_one f a
    have hst := topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point f a hc
    rw [ringKrullDim_stalk_eq_coheight] at hst
    exact_mod_cast hst.symm.trans hdim
  have hn : ¬ IsMax a := coheight_ne_zero.mp (by rw [ha]; exact one_ne_zero)
  obtain ⟨b, hab⟩ := not_isMax_iff.mp hn
  have hs : StrictMono (q.fiberι y) := by
    intro c d hcd
    refine ⟨hcd.le.map (q.fiberι y).continuous, ?_⟩
    intro hdc
    exact hcd.not_ge ((q.fiberι y).isEmbedding.isInducing.specializes_iff.mp hdc)
  have hxb : x < q.fiberι y b := by
    simpa only [a, y, Scheme.Hom.fiberι_asFiber] using hs hab
  have hb : coheight (q.fiberι y b) = 0 :=
    Order.lt_one_iff.mp ((coheight_le_coe_iff.mp hx.le) _ hxb)
  have hgeneric := mem_genericPoints_of_generalizingMap (Flat.generalizingMap q)
    ((mem_genericPoints_iff_isMax X _).mpr (coheight_eq_zero.mp hb))
  have he : q (q.fiberι y b) = q x := by
    have hm : q.fiberι y b ∈ Set.range (q.fiberι y) := ⟨b, rfl⟩
    rw [q.range_fiberι y] at hm
    exact hm
  rwa [he] at hgeneric

/-- A finite closed support at a codimension-one point of a smooth relative
curve lies over a generic point of the base. -/
theorem image_mem_genericPoints_of_coheight_one_finite_closed_support
    {D X S : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (q : X ⟶ S) [SmoothOfRelativeDimension 1 q] [IsFinite (i ≫ q)]
    (x : D) (hx : coheight (i x) = 1) : q (i x) ∈ genericPoints S := by
  let e := i.residueFieldMap x
  have hsurj : Function.Surjective e := by
    intro z
    obtain ⟨a, rfl⟩ := D.residue_surjective x z
    obtain ⟨b, hb⟩ := i.stalkMap_surjective x a
    refine ⟨(X.residue (i x)).hom b, ?_⟩
    simpa only [e, CommRingCat.comp_apply, hb] using
      congrArg (fun f : X.presheaf.stalk (i x) ⟶ D.residueField x => f.hom b)
        (Scheme.residue_residueFieldMap i x)
  let : IsIso e := (ConcreteCategory.isIso_iff_bijective e).mpr ⟨e.hom.injective, hsurj⟩
  have : IsFinite (Spec.map ((i ≫ q).residueFieldMap x)) :=
    (IsFinite.SpecMap_iff _).mpr (residueField_finite_of_locallyQuasiFinite (i ≫ q) x)
  have he : Spec.map (q.residueFieldMap (i x)) =
      inv (Spec.map e) ≫ Spec.map ((i ≫ q).residueFieldMap x) := by
    rw [Scheme.residueFieldMap_comp]
    erw [Spec.map_comp, IsIso.inv_hom_id_assoc]
  have hfin : IsFinite (Spec.map (q.residueFieldMap (i x))) := by
    rw [he]
    infer_instance
  let : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  exact image_mem_genericPoints_of_coheight_one_closed_fiber q (i x) hx
    ((isClosed_asFiber_iff_finite_residueField q (i x)).mpr ((IsFinite.SpecMap_iff _).mp hfin))

end AlgebraicGeometry.Scheme

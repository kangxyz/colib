/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Exactness of the bounded-above projective model

The actual projective complexes are stable under shifts and mapping
cones. Their existing quotient equivalence and the application of an
additive coefficient functor therefore preserve distinguished triangles.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex ComplexShape
open scoped ZeroObject

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "c" => ComplexShape.up ℤ

private theorem boundedAboveProjective_of_shift
    {P : HomotopyCategory (PresheafWithTransfers.{u + 1} k) c}
    (hP : boundedAboveProjectiveCondition k P) (n : ℤ) :
    boundedAboveProjectiveCondition k (P⟦n⟧) := by
  let C := PresheafWithTransfers.{u + 1} k
  let Q := HomotopyCategory.quotient C c
  let K : CochainComplex C ℤ := P.as
  obtain ⟨b, hb, hproj⟩ := hP
  let : K.IsStrictlyLE b := hb
  change boundedAboveProjectiveCondition k ((Q.obj K)⟦n⟧)
  rw [HomotopyCategory.shift_quotient_obj]
  refine ⟨b - n, K.isStrictlyLE_shift b n _ (by omega), fun i => ?_⟩
  exact Projective.of_iso (K.shiftFunctorObjXIso n i (i + n) rfl).symm (hproj (i + n))

private theorem boundedAboveProjective_mappingCone
    {K L : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ} (f : K ⟶ L)
    (hK : boundedAboveProjectiveCondition k ((HomotopyCategory.quotient _ c).obj K))
    (hL : boundedAboveProjectiveCondition k ((HomotopyCategory.quotient _ c).obj L)) :
    boundedAboveProjectiveCondition k
      ((HomotopyCategory.quotient _ c).obj (CochainComplex.mappingCone f)) := by
  obtain ⟨a, ha, hK'⟩ := hK
  obtain ⟨b, hb, hL'⟩ := hL
  let : K.IsStrictlyLE a := ha
  let : L.IsStrictlyLE b := hb
  refine ⟨max a b, (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi => ?_), fun i => ?_⟩
  · change IsZero ((CochainComplex.mappingCone f).X i)
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨K.isZero_of_isStrictlyLE a (i + 1) (by omega),
      L.isZero_of_isStrictlyLE b i (by omega)⟩
  · let : Projective (K.X (i + 1)) := hK' (i + 1)
    let : Projective (L.X i) := hL' i
    exact Projective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1)
      (by simp)).symm inferInstance

private instance : (boundedAboveProjectiveCondition k).ContainsZero where
  exists_zero := by
    let C := PresheafWithTransfers.{u + 1} k
    let Q := HomotopyCategory.quotient C c
    let K : CochainComplex C ℤ := 0
    let h : IsZero K := Limits.isZero_zero _
    let hb : K.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff K 0).2
      (fun i _ => (HomologicalComplex.eval C c i).map_isZero h)
    exact ⟨Q.obj K, Q.map_isZero h, 0, hb,
      fun i => ((HomologicalComplex.eval C c i).map_isZero h).projective⟩

private instance : (boundedAboveProjectiveCondition k).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ h => boundedAboveProjective_of_shift k h n⟩

private instance : (boundedAboveProjectiveCondition k).IsTriangulatedClosed₃ where
  ext₃' T hT hX hY := by
    let Q := HomotopyCategory.quotient (PresheafWithTransfers.{u + 1} k) c
    obtain ⟨g, hg⟩ := Q.map_surjective T.mor₁
    let U := CochainComplex.mappingCone.triangleh g
    have hU : U ∈ distTriang _ := HomotopyCategory.mappingCone_triangleh_distinguished g
    let e := isoTriangleOfIso₁₂ U T hU hT (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans (hg.trans (Category.id_comp _).symm))
    exact ⟨U.obj₃, boundedAboveProjective_mappingCone k g hX hY,
      ⟨Triangle.π₃.mapIso e.symm⟩⟩

instance : (boundedAboveProjectiveCondition k).IsTriangulated where
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

private abbrev projectiveMinusInclusion
    (F : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k) [F.Additive] :
    projectiveHomotopyMapToDerivedMinus k F ⋙ DerivedCategory.Minus.ι ≅
      (boundedAboveProjectiveCondition k).ι ⋙
        F.mapHomotopyCategory c ⋙ DerivedCategory.Qh :=
  Iso.refl _

private abbrev projectiveQuotientInclusion :
    projectiveHomotopyToDerivedMinus k ⋙ DerivedCategory.Minus.ι ≅
      (boundedAboveProjectiveCondition k).ι ⋙ DerivedCategory.Qh :=
  Iso.refl _

@[no_expose]
instance projectiveHomotopyToDerivedMinusCommShift :
    (projectiveHomotopyToDerivedMinus k).CommShift ℤ :=
  Functor.CommShift.ofComp (projectiveQuotientInclusion k) ℤ

instance projectiveHomotopyToDerivedMinus_isTriangulated :
    (projectiveHomotopyToDerivedMinus k).IsTriangulated := by
  let e := projectiveQuotientInclusion k
  let : (projectiveHomotopyToDerivedMinus k).CommShift ℤ :=
    Functor.CommShift.ofComp e ℤ
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).2 inferInstance

@[no_expose]
instance projectiveHomotopyMapToDerivedMinusCommShift
    (F : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k)
    [F.Additive] : (projectiveHomotopyMapToDerivedMinus k F).CommShift ℤ :=
  Functor.CommShift.ofComp (projectiveMinusInclusion k F) ℤ

instance (F : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k)
    [F.Additive] : (projectiveHomotopyMapToDerivedMinus k F).IsTriangulated := by
  let e := projectiveMinusInclusion k F
  let : (projectiveHomotopyMapToDerivedMinus k F).CommShift ℤ :=
    Functor.CommShift.ofComp e ℤ
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  let : (F.mapHomotopyCategory c).IsTriangulated := inferInstance
  let : (F.mapHomotopyCategory c ⋙ DerivedCategory.Qh).IsTriangulated := inferInstance
  exact (Functor.isTriangulated_iff_comp_right e).2 inferInstance

@[no_expose]
instance : ((boundedAboveProjectiveEquivalence k).functor).CommShift ℤ := by
  unfold boundedAboveProjectiveEquivalence
  exact projectiveHomotopyToDerivedMinusCommShift k

instance : ((boundedAboveProjectiveEquivalence k).functor).IsTriangulated := by
  unfold boundedAboveProjectiveEquivalence
  exact projectiveHomotopyToDerivedMinus_isTriangulated k

@[no_expose]
instance : ((boundedAboveProjectiveEquivalence k).inverse).CommShift ℤ :=
  (boundedAboveProjectiveEquivalence k).commShiftInverse ℤ

instance : ((boundedAboveProjectiveEquivalence k).inverse).IsTriangulated := by
  let e := boundedAboveProjectiveEquivalence k
  let : e.inverse.CommShift ℤ := e.commShiftInverse ℤ
  let : e.CommShift ℤ := e.commShift_of_functor ℤ
  let : e.IsTriangulated := Equivalence.IsTriangulated.mk' e inferInstance
  infer_instance

@[no_expose]
instance (F : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k)
    [F.Additive] : (projectiveDerivedMinusFunctor k F).CommShift ℤ := by
  unfold projectiveDerivedMinusFunctor
  infer_instance

instance (F : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k)
    [F.Additive] : (projectiveDerivedMinusFunctor k F).IsTriangulated := by
  unfold projectiveDerivedMinusFunctor
  infer_instance

end AlgebraicGeometry.PresheafWithTransfers

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.TensorClosure
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.ReducedTorusObject
public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.Stable
public import Colib.CategoryTheory.Triangulated.SignedShift
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift

/-! # The tensor on effective geometric motives -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme
open scoped MonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

set_option quotPrecheck false in
local notation "E" => EffectiveMotivesMinus k
set_option quotPrecheck false in
local notation "G" => EffectiveGeometricMotives k
set_option quotPrecheck false in
local notation "P" => isEffectiveGeometric k
set_option quotPrecheck false in
local notation "J" => effectiveGeometricMotivesInclusion k
set_option quotPrecheck false in
local notation "B" => SmoothSite.base (Spec (CommRingCat.of k))
set_option quotPrecheck false in
local notation "M" => effectiveMotive k

/-- The Lefschetz object is geometric by the original reduced-torus retract and shift. -/
abbrev geometricEffectiveLefschetzMotive : G :=
  ⟨effectiveLefschetzMotive k,
    isEffectiveGeometric_reducedTorusShift k 1 (isEffectiveGeometric_effectiveMotive k (Cor.mk B))⟩

variable [MonoidalCategory (EffectiveMotivesMinus k)]
  [ObjectProperty.IsMonoidal (isEffectiveGeometric k)]

/-- The canonical abelian structure on the sheaves with transfers. -/
local instance effectiveGeometricSheafAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The inclusion of effective geometric motives commutes with the inherited shift. -/
local instance effectiveGeometricInclusionCommShift :
    (effectiveGeometricMotivesInclusion k).CommShift ℤ :=
  inferInstanceAs ((isEffectiveGeometric k).ι.CommShift ℤ)

local instance : (effectiveGeometricMotivesInclusion k).IsTriangulated :=
  inferInstanceAs ((isEffectiveGeometric k).ι.IsTriangulated)

/-- The inclusion preserves the right tensor on the original full subcategory. -/
def geometricTensorRightCompIso (A : G) : tensorRight A ⋙ J ≅ J ⋙ tensorRight A.obj :=
  (Functor.Monoidal.commTensorRight (J) A).symm

/-- The inclusion preserves the left tensor on the original full subcategory. -/
def geometricTensorLeftCompIso (A : G) : tensorLeft A ⋙ J ≅ J ⋙ tensorLeft A.obj :=
  (Functor.Monoidal.commTensorLeft (J) A).symm

/-- Compare the two geometric transitions after the literal effective inclusion. -/
def geometricTensorRightLefschetzIsoPostcomp
    (e : tensorRight (effectiveLefschetzMotive k) ≅
      effectiveReducedTorusTensorFunctor k ⋙ shiftFunctor E (1 : ℤ)) :
    tensorRight (geometricEffectiveLefschetzMotive k) ⋙ J ≅ geometricLefschetzTensor k ⋙ J := by
  let L := geometricEffectiveLefschetzMotive k
  let j := J
  let h₁ := geometricTensorRightCompIso k L
  let h₂ := Functor.isoWhiskerLeft j e
  have h₃ : j ⋙ (effectiveReducedTorusTensorFunctor k ⋙ shiftFunctor E (1 : ℤ)) ≅
      geometricLefschetzTensor k ⋙ j := by
    let R := geometricReducedTorusTensor k
    change j ⋙ (effectiveReducedTorusTensorFunctor k ⋙ shiftFunctor E (1 : ℤ)) ≅
      (R ⋙ shiftFunctor G (1 : ℤ)) ⋙ j
    exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((isEffectiveGeometric k).liftCompιIso (j ⋙ effectiveReducedTorusTensorFunctor k)
          (fun K => isEffectiveGeometric_effectiveReducedTorusTensor k K.property)).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R (j.commShiftIso (1 : ℤ)).symm ≪≫
      (Functor.associator _ _ _).symm
  exact h₁ ≪≫ h₂ ≪≫ h₃

/-- A compatible ambient right tensor comparison restricts to the original geometric twist. -/
@[no_expose]
def geometricTensorRightLefschetzIso
    (e : tensorRight (effectiveLefschetzMotive k) ≅
      effectiveReducedTorusTensorFunctor k ⋙ shiftFunctor E (1 : ℤ)) :
    tensorRight (geometricEffectiveLefschetzMotive k) ≅ geometricLefschetzTensor k :=
  Functor.fullyFaithfulCancelRight (J) (geometricTensorRightLefschetzIsoPostcomp k e)

/-- Right tensor on the geometric subcategory uses the actual ambient shift comparison. -/
@[instance_reducible]
def geometricTensorRightCommShift (L : G) [(tensorRight L.obj).CommShift ℤ] :
    (tensorRight L).CommShift ℤ :=
  Functor.CommShift.ofComp (geometricTensorRightCompIso k L) ℤ

/-- Left tensor on the geometric subcategory uses the actual ambient shift comparison. -/
@[instance_reducible]
def geometricTensorLeftCommShift (L : G) [(tensorLeft L.obj).CommShift ℤ] :
    (tensorLeft L).CommShift ℤ :=
  Functor.CommShift.ofComp (geometricTensorLeftCompIso k L) ℤ

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}] in
/-- Right tensor is exact on effective geometric motives. -/
theorem geometricTensorRight_isTriangulated (L : G)
    [(tensorRight L.obj).CommShift ℤ] [(tensorRight L.obj).IsTriangulated] :
    let := geometricTensorRightCommShift k L
    (tensorRight L).IsTriangulated := by
  let e := geometricTensorRightCompIso k L
  let := geometricTensorRightCommShift k L
  let := Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).2 inferInstance

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}] in
/-- Left tensor is exact on effective geometric motives. -/
theorem geometricTensorLeft_isTriangulated (L : G)
    [(tensorLeft L.obj).CommShift ℤ] [(tensorLeft L.obj).IsTriangulated] :
    let := geometricTensorLeftCommShift k L
    (tensorLeft L).IsTriangulated := by
  let e := geometricTensorLeftCompIso k L
  let := geometricTensorLeftCommShift k L
  let := Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).2 inferInstance

section Shift

variable [∀ A : EffectiveMotivesMinus k, (tensorLeft A).CommShift ℤ]
  [∀ A : EffectiveMotivesMinus k, (tensorRight A).CommShift ℤ]

attribute [local instance] geometricTensorRightCommShift geometricTensorLeftCommShift

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}] in
/-- The literal geometric inclusion preserves the ambient one-variable tensor shifts. -/
theorem geometricInclusionMonoidalCommShift :
    Functor.LaxMonoidal.CommShift (J) ℤ := by
  let I := J
  refine ⟨fun Y => ?_, fun X => ?_⟩
  · let u := geometricTensorRightCompIso k Y
    have hu : u.inv = Functor.LaxMonoidal.μNatTransFst I Y := by
      ext X
      rfl
    let : NatTrans.CommShift u.hom ℤ := Functor.CommShift.ofComp_compatibility u ℤ
    exact hu ▸ NatTrans.CommShift.of_iso_inv u ℤ
  · let u := geometricTensorLeftCompIso k X
    have hu : u.inv = Functor.LaxMonoidal.μNatTransSnd I X := by
      ext Y
      rfl
    let : NatTrans.CommShift u.hom ℤ := Functor.CommShift.ofComp_compatibility u ℤ
    exact hu ▸ NatTrans.CommShift.of_iso_inv u ℤ

set_option maxHeartbeats 650000 in
-- The signed shift is carried through the original inclusion.
omit [∀ A : EffectiveMotivesMinus k, (tensorLeft A).CommShift ℤ] in
/-- The postcomposition of the geometric comparison preserves the original signed shift. -/
theorem geometricTensorRightLefschetzIsoPostcomp_commShift
    (e : tensorRight (effectiveLefschetzMotive k) ≅ effectiveLefschetzTwistFunctor k)
    (he : NatTrans.CommShift e.hom ℤ) :
    NatTrans.CommShift (geometricTensorRightLefschetzIsoPostcomp k e).hom ℤ := by
  let J₀ := J
  let R := geometricReducedTorusTensor k
  let S₀ := effectiveReducedTorusTensorFunctor k
  let T := tensorRight (geometricEffectiveLefschetzMotive k)
  let U := tensorRight (effectiveLefschetzMotive k)
  let a : T ⋙ J₀ ≅ J₀ ⋙ U :=
    geometricTensorRightCompIso k (geometricEffectiveLefschetzMotive k)
  let : NatTrans.CommShift a.hom ℤ := Functor.CommShift.ofComp_compatibility a ℤ
  let b : R ⋙ J₀ ≅ J₀ ⋙ S₀ := (isEffectiveGeometric k).liftCompιIso (J₀ ⋙ S₀)
    (fun K => isEffectiveGeometric_effectiveReducedTorusTensor k K.property)
  let : NatTrans.CommShift b.hom ℤ := inferInstanceAs
    (NatTrans.CommShift
      ((isEffectiveGeometric k).liftCompιIso (J₀ ⋙ S₀)
        (fun K => isEffectiveGeometric_effectiveReducedTorusTensor k K.property)).hom ℤ)
  let : NatTrans.CommShift b.inv ℤ := NatTrans.CommShift.of_iso_inv b ℤ
  let : NatTrans.CommShift (J₀.commShiftIso (1 : ℤ)).hom ℤ :=
    commShiftIso_signedShift G J₀ 1
  let : NatTrans.CommShift (J₀.commShiftIso (1 : ℤ)).inv ℤ :=
    NatTrans.CommShift.of_iso_inv (J₀.commShiftIso (1 : ℤ)) ℤ
  let := he
  let f₁ := Functor.whiskerLeft J₀ e.hom
  let f₂ := (Functor.associator J₀ S₀ (shiftFunctor E (1 : ℤ))).inv
  let f₃ := Functor.whiskerRight b.inv (shiftFunctor E (1 : ℤ))
  let f₄ := (Functor.associator R J₀ (shiftFunctor E (1 : ℤ))).hom
  let f₅ := Functor.whiskerLeft R (J₀.commShiftIso (1 : ℤ)).inv
  let f₆ := (Functor.associator R (shiftFunctor G (1 : ℤ)) J₀).inv
  let : NatTrans.CommShift f₁ ℤ := inferInstanceAs
    (NatTrans.CommShift (Functor.whiskerLeft J₀ e.hom) ℤ)
  let : NatTrans.CommShift (Functor.associator J₀ S₀ (shiftFunctor E (1 : ℤ))).hom ℤ :=
    NatTrans.CommShift.associator _ _ ℤ
  let : NatTrans.CommShift f₂ ℤ :=
    NatTrans.CommShift.of_iso_inv (Functor.associator J₀ S₀ (shiftFunctor E (1 : ℤ))) ℤ
  let : NatTrans.CommShift f₃ ℤ := NatTrans.CommShift.whiskerRight b.inv _ ℤ
  let : NatTrans.CommShift f₄ ℤ := NatTrans.CommShift.associator _ _ ℤ
  let : NatTrans.CommShift f₅ ℤ := inferInstanceAs
    (NatTrans.CommShift (Functor.whiskerLeft R (J₀.commShiftIso (1 : ℤ)).inv) ℤ)
  let : NatTrans.CommShift (Functor.associator R (shiftFunctor G (1 : ℤ)) J₀).hom ℤ :=
    NatTrans.CommShift.associator _ _ ℤ
  let : NatTrans.CommShift f₆ ℤ :=
    NatTrans.CommShift.of_iso_inv (Functor.associator R (shiftFunctor G (1 : ℤ)) J₀) ℤ
  let : NatTrans.CommShift (f₅ ≫ f₆) ℤ := NatTrans.CommShift.comp f₅ f₆ ℤ
  let : NatTrans.CommShift (f₄ ≫ f₅ ≫ f₆) ℤ := NatTrans.CommShift.comp f₄ (f₅ ≫ f₆) ℤ
  let : NatTrans.CommShift (f₃ ≫ f₄ ≫ f₅ ≫ f₆) ℤ :=
    NatTrans.CommShift.comp f₃ (f₄ ≫ f₅ ≫ f₆) ℤ
  let : NatTrans.CommShift (f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆) ℤ :=
    NatTrans.CommShift.comp f₂ (f₃ ≫ f₄ ≫ f₅ ≫ f₆) ℤ
  let : NatTrans.CommShift (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆) ℤ :=
    NatTrans.CommShift.comp f₁ (f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆) ℤ
  change NatTrans.CommShift (a.hom ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆) ℤ
  exact NatTrans.CommShift.comp a.hom (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆) ℤ

omit [∀ A : EffectiveMotivesMinus k, (tensorLeft A).CommShift ℤ] in
/-- The lift of the ambient Lefschetz comparison intertwines shifts
when its original postcomposition with the inclusion does. -/
theorem geometricTensorRightLefschetzIso_postcomp_commShift
    (e : tensorRight (effectiveLefschetzMotive k) ≅
      effectiveReducedTorusTensorFunctor k ⋙ shiftFunctor E (1 : ℤ))
    (he : NatTrans.CommShift (geometricTensorRightLefschetzIsoPostcomp k e).hom ℤ) :
    NatTrans.CommShift (Functor.whiskerRight (geometricTensorRightLefschetzIso k e).hom (J)) ℤ := by
  have hh : Functor.whiskerRight (geometricTensorRightLefschetzIso k e).hom (J) =
      (geometricTensorRightLefschetzIsoPostcomp k e).hom := by
    apply NatTrans.ext
    funext X
    exact (J).map_preimage _
  exact hh.symm ▸ he

end Shift

end AlgebraicGeometry.MotivicHomotopy

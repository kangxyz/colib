/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedTransformationCone
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenSupport
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.PerfectShiftSign
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula

/-! # The K-class of the original supported cone -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen AlgebraicGeometry
open CochainComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
local notation "P" => RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
local notation "Perf" => ObjectProperty.FullSubcategory P
local notation "W" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace


set_option maxHeartbeats 800000 in
-- The native functor type includes the same perfect support predicate at both ends.
/-- The actual inclusion of the target in its cone, after forgetting support. -/
def perfectSupportedTransformationConeInclusion
    {F G : Perf ⥤ Perf} (α : NatTrans F G)
    (hα : ∀ K : Perf, (perfectOpenWeakWaldhausen j).weq (NatTrans.app α K)) :
    @Quiver.Hom (Perf ⥤ Perf) _ G
      (@perfectSupportedTransformationCone X U j inferInstance F G α hα ⋙
        perfectSupportedInclusion j) where
  app K := ObjectProperty.homMk (mappingCone.inr (NatTrans.app α K).hom)
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (mappingCone.triangleMap (NatTrans.app α K).hom (α.app L).hom (F.map f).hom
      (G.map f).hom (congrArg (fun g => g.hom) (α.naturality f).symm)).comm₂.symm

set_option maxHeartbeats 800000 in
-- The native functor type includes the same perfect support predicate at both ends.
/-- The signed quotient of the actual cone by its target. -/
def perfectSupportedTransformationConeQuotient
    {F G : Perf ⥤ Perf} (α : NatTrans F G)
    (hα : ∀ K : Perf, (perfectOpenWeakWaldhausen j).weq (NatTrans.app α K)) :
    @Quiver.Hom (Perf ⥤ Perf) _
      (@perfectSupportedTransformationCone X U j inferInstance F G α hα ⋙
        perfectSupportedInclusion j) (F ⋙ RingedSpace.perfectShift X.toRingedSpace 1) where
  app K := ObjectProperty.homMk (mappingCone.triangle (NatTrans.app α K).hom).mor₃
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (mappingCone.triangleMap (NatTrans.app α K).hom (α.app L).hom (F.map f).hom
      (G.map f).hom (congrArg (fun g => g.hom) (α.naturality f).symm)).comm₃.symm

theorem perfectSupportedTransformationConeInclusion_quotient
    {F G : Perf ⥤ Perf} (α : NatTrans F G)
    (hα : ∀ K : Perf, (perfectOpenWeakWaldhausen j).weq (NatTrans.app α K)) :
    perfectSupportedTransformationConeInclusion j α hα ≫
      perfectSupportedTransformationConeQuotient j α hα = 0 := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact (mappingCone.triangleRotateShortComplex (NatTrans.app α K).hom).zero


set_option maxHeartbeats 800000 in
-- Composing native exact structures elaborates the perfect cone and shift simultaneously.
theorem perfectSupportedTransformationCone_cofibrationSequence
    {F G : Perf ⥤ Perf} (α : NatTrans F G)
    (hF : IsExact (W).cof (W).weq (W).cof (W).weq F)
    (hG : IsExact (W).cof (W).weq (W).cof (W).weq G)
    (hα : ∀ K : Perf, (perfectOpenWeakWaldhausen j).weq (NatTrans.app α K))
    (hC : IsExact (W).cof (W).weq (perfectSupportedWaldhausen j).cof
      (perfectSupportedWaldhausen j).weq
      (@perfectSupportedTransformationCone X U j inferInstance F G α hα)) :
    Additivity.IsCofibrationSequence W W (perfectSupportedTransformationConeInclusion j α hα)
      (perfectSupportedTransformationConeQuotient j α hα) :=
  RingedSpace.perfectCofibrationSequence_of_shortExact W X.toRingedSpace _ _
    (perfectSupportedTransformationConeInclusion_quotient j α hα)
    hG (hC.comp (perfectSupportedInclusion_isExact j))
    (hF.comp (RingedSpace.perfectShift_exact X.toRingedSpace 1))
    (fun K => by
      change (mappingCone.triangleRotateShortComplex (NatTrans.app α K).hom).ShortExact
      exact mappingCone_triangle_shortExact (NatTrans.app α K).hom)

set_option maxHeartbeats 800000 in
-- The K-map comparison elaborates the exact structures of both composite functors.
/-- Forgetting support retains the actual target-minus-source K-class in every degree. -/
theorem perfectSupportedTransformationCone_KMap_forget
    {F G : Perf ⥤ Perf} (α : NatTrans F G)
    (hF : IsExact (W).cof (W).weq (W).cof (W).weq F)
    (hG : IsExact (W).cof (W).weq (W).cof (W).weq G)
    (hα : ∀ K : Perf, (perfectOpenWeakWaldhausen j).weq (NatTrans.app α K))
    (hC : IsExact (W).cof (W).weq (perfectSupportedWaldhausen j).cof
      (perfectSupportedWaldhausen j).weq
      (@perfectSupportedTransformationCone X U j inferInstance F G α hα))
    (n : ℕ) (a : (W).K n) :
    perfectSupportedKMap j n (KMap hC n a) = KMap hG n a * (KMap hF n a)⁻¹ := by
  let : HasBinaryCoproducts Perf := Additivity.hasBinaryCoproducts W
  have h := Additivity.KMap_additivity_mul W W _ _
    (perfectSupportedTransformationCone_cofibrationSequence j α hF hG hα hC) n a
  change KMap (hC.comp (perfectSupportedInclusion_isExact j)) n a =
    KMap hG n a * KMap (hF.comp (RingedSpace.perfectShift_exact X.toRingedSpace 1)) n a at h
  rw [← KMap_comp_KMap hC (perfectSupportedInclusion_isExact j) n,
    ← KMap_comp_KMap hF (RingedSpace.perfectShift_exact X.toRingedSpace 1) n] at h
  exact h.trans (congrArg (KMap hG n a * ·)
    (RingedSpace.perfectShift_KMap_one_apply X.toRingedSpace n (KMap hF n a)))

end AlgebraicGeometry.Scheme.Modules

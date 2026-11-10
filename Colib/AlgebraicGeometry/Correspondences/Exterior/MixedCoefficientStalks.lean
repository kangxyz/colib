/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedCoefficientChart
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalKoszulTor

/-!
# The actual scalar paths through the mixed coefficient chart

At a point of the native mixed incidence, the original middle-stalk map followed
by the native support-stalk map equals the pointed mixed-pair stalk map followed
by the open chart's stalk isomorphism. The equality retains the original middle
self-product stalk, the actual full support-product stalk and both point
transports. This identifies the scalar map on which a common regular list must
be evaluated. It does not assert that such a common list has been constructed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

private theorem mixed_transported_stalkMap_comp {A B C : Scheme.{u}}
    (i : A ⟶ B) (j : B ⟶ C) (a : A) (b : B) (c : C)
    (hab : b = i a) (hbc : c = j b) :
    ((C.presheaf.stalkCongr (Inseparable.of_eq hbc)).hom ≫ j.stalkMap b) ≫
      ((B.presheaf.stalkCongr (Inseparable.of_eq hab)).hom ≫ i.stalkMap a) =
    (C.presheaf.stalkCongr (Inseparable.of_eq (hbc.trans (congrArg j hab)))).hom ≫
      (i ≫ j).stalkMap a := by
  subst b
  subst c
  simp [TopCat.Presheaf.stalkCongr, Scheme.Hom.stalkMap_comp]

private theorem mixed_transported_stalkMap_congr {A B : Scheme.{u}}
    (i j : A ⟶ B) (hij : i = j) (a : A) (b : B)
    (hi : b = i a) (hj : b = j a) :
    (B.presheaf.stalkCongr (Inseparable.of_eq hi)).hom ≫ i.stalkMap a =
      (B.presheaf.stalkCongr (Inseparable.of_eq hj)).hom ≫ j.stalkMap a := by
  subst j
  rfl

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X U).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Y U).hom
local notation3 (prettyPrint := false) "a" => nativeParameterGraphPoint X T U ψ t
local notation3 (prettyPrint := false) "b" => nativeExteriorPoint X Y U z hz
local notation3 (prettyPrint := false) "q" => nativeMixedCoefficientChart X Y T U ψ z hz t
local notation3 (prettyPrint := false) "m" =>
  nativeMixedCoefficientPair X Y T U (integralComponentAt z) ψ

/-- The actual open chart induces an isomorphism on every support-product stalk. -/
def nativeMixedCoefficientChartStalkIso (d : nativeMixedGraphSupportProduct X Y T U ψ z hz t) :
    (nativeMixedCoefficient X Y T U (integralComponentAt z)).presheaf.stalk (q d) ≅
      (nativeMixedGraphSupportProduct X Y T U ψ z hz t).presheaf.stalk d :=
  asIso ((q).stalkMap d)

/-- The displayed stalk isomorphism is literally the open chart's stalk map. -/
@[simp]
theorem nativeMixedCoefficientChartStalkIso_hom
    (d : nativeMixedGraphSupportProduct X Y T U ψ z hz t) :
    (nativeMixedCoefficientChartStalkIso X Y T U ψ z hz t d).hom = (q).stalkMap d := rfl

variable (x : nativeMixedGraphIncidence X Y T U ψ z hz t)

local notation3 (prettyPrint := false) "p" => correspondenceIncidenceAmbientInclusion f g h a b x
local notation3 (prettyPrint := false) "d" => correspondenceIncidenceToSupportProduct f g h a b x

/-- The literal chart uses exactly the original incidence's middle self-product point. -/
theorem nativeMixedCoefficient_middlePoint :
    correspondenceMiddlePair f g h p = m (q d) := by
  simp only [correspondenceIncidenceAmbientInclusion, Scheme.Hom.comp_apply]
  rw [correspondenceIncidence_ambient_point_eq f g h a b x]
  simpa only [Scheme.Hom.comp_apply] using
    (congrArg (fun e => e d)
      (nativeMixedCoefficientChart_middlePair X Y T U ψ z hz t)).symm

/-- The pointed mixed-pair map starts at the original native middle self-product stalk. -/
def nativeMixedCoefficientMiddleStalkMap :
    (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h p) ⟶
      (nativeMixedCoefficient X Y T U (integralComponentAt z)).presheaf.stalk (q d) :=
  ((pullback g g).presheaf.stalkCongr
      (Inseparable.of_eq (nativeMixedCoefficient_middlePoint X Y T U ψ z hz t x))).hom ≫
    (m).stalkMap (q d)

/-- The original middle-to-support scalar map factors through the actual open coefficient
chart, including the original incidence point transport. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/GraphInterchangeStalks.lean:155-194"
  "adaptation" "Equality of the actual original native scalar paths through the open \
    mixed coefficient chart"]
theorem nativeMixedCoefficientMiddleStalkMap_comp :
    (((q).stalkMap d).hom).comp
      (nativeMixedCoefficientMiddleStalkMap X Y T U ψ z hz t x).hom =
    (correspondenceIncidenceSupportStalkMap f g h a b x).comp
      ((correspondenceMiddlePair f g h).stalkMap p).hom := by
  let j := correspondenceSupportProductInclusion f g h a b
  let β := correspondenceMiddlePair f g h
  have hp : p = j d := by
    simpa only [j, correspondenceIncidenceAmbientInclusion, Scheme.Hom.comp_apply] using
      correspondenceIncidence_ambient_point_eq f g h a b x
  have he : j ≫ β = q ≫ m :=
    (nativeMixedCoefficientChart_middlePair X Y T U ψ z hz t).symm
  have hc := mixed_transported_stalkMap_comp j β d p (β p) hp rfl
  have hfinal := mixed_transported_stalkMap_congr (j ≫ β) (q ≫ m) he d (β p)
    (congrArg β hp) (nativeMixedCoefficient_middlePoint X Y T U ψ z hz t x)
  have hcat := hc.trans hfinal
  change (((pullback g g).presheaf.stalkCongr
      (Inseparable.of_eq (nativeMixedCoefficient_middlePoint X Y T U ψ z hz t x))).hom ≫
      (m).stalkMap (q d) ≫ (q).stalkMap d).hom =
    ((β.stalkMap p) ≫
      ((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
        (Inseparable.of_eq hp)).hom ≫ j.stalkMap d).hom
  simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp, Scheme.Hom.stalkMap_comp, Category.assoc] using
      (congrArg (fun e => e.hom) hcat).symm

end Stacks.Chow

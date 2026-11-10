/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceIso
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleDiagonal

/-!
# The actual open coefficient chart for mixed graph incidence

The product of the native parameter-graph component and the native exterior
support maps openly into `(X × T) × (W × U)`. Its first map is the graph
component's source projection and its second map is the inverse of the native
exterior-support isomorphism. The chart preserves the actual middle pair as a
scheme morphism. Neither the parameter map nor the original support projection
is assumed flat. No matching-component range condition is needed here.

The literal coefficient scheme and its mixed pair are defined over an arbitrary
base. The open chart uses the existing normal-component theorem over a field and
the existing support isomorphism for a geometrically integral target parameter.
This is geometry for a later common-diagonal-list argument, not a Tor equation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

section Coefficient

variable {S : Scheme.{u}} (X Y T U : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData)

/-- The literal coefficient scheme `(X × T) ×_S (W × U)`.
The second structure map is displayed through its actual exterior source map. -/
abbrev nativeMixedCoefficient : Scheme.{u} :=
  pullback (SmoothSite.product X T).hom
    (exteriorIdentitySource X Y U W ≫ (SmoothSite.product X U).hom)

/-- The second structural map is the ordinary structural map of `W ×_S U`. -/
theorem nativeMixedCoefficient_second_structure :
    exteriorIdentitySource X Y U W ≫ (SmoothSite.product X U).hom =
      pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) U.hom ≫
        exteriorSupportSourceProjection X Y W ≫ X.hom := by
  simp only [SmoothSite.product_hom, ← Category.assoc, exteriorIdentitySource_fst]

/-- The mixed pair sends `((x,t),(w,u))` to `((x,ψ(t)),(p(w),u))`. -/
def nativeMixedCoefficientPair (ψ : T ⟶ U) :
    nativeMixedCoefficient X Y T U W ⟶
      pullback (SmoothSite.product X U).hom (SmoothSite.product X U).hom :=
  pullback.map _ _ _ _ (SmoothSite.productMap (𝟙 X) ψ).left
    (exteriorIdentitySource X Y U W) (𝟙 S)
    (by simpa using (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 X) ψ)).symm)
    (by simp)

@[reassoc (attr := simp)]
theorem nativeMixedCoefficientPair_fst (ψ : T ⟶ U) :
    nativeMixedCoefficientPair X Y T U W ψ ≫
      pullback.fst (pullback.fst X.hom U.hom ≫ X.hom)
        (pullback.fst X.hom U.hom ≫ X.hom) =
      pullback.fst _ _ ≫ (SmoothSite.productMap (𝟙 X) ψ).left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem nativeMixedCoefficientPair_snd (ψ : T ⟶ U) :
    nativeMixedCoefficientPair X Y T U W ψ ≫
      pullback.snd (pullback.fst X.hom U.hom ≫ X.hom)
        (pullback.fst X.hom U.hom ≫ X.hom) =
      pullback.snd _ _ ≫ exteriorIdentitySource X Y U W :=
  pullback.lift_snd _ _ _

end Coefficient

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)

/-- The actual support product underlying the native mixed incidence coefficient ring. -/
abbrev nativeMixedGraphSupportProduct : Scheme.{u} :=
  correspondenceSupportProduct (SmoothSite.product X T).hom (SmoothSite.product X U).hom
    (SmoothSite.product Y U).hom (nativeParameterGraphPoint X T U ψ t)
    (nativeExteriorPoint X Y U z hz)

omit [GeometricallyIntegral U.hom] in
/-- The graph-source projection preserves the actual support structure map. -/
theorem nativeMixedCoefficientChart_source_structure :
    (integralComponentAt (nativeParameterGraphPoint X T U ψ t)).subschemeι ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product X U).hom ≫
          (SmoothSite.product X U).hom =
      nativeParameterGraphSource X T U ψ t ≫ (SmoothSite.product X T).hom := by
  simpa only [nativeParameterGraphSource, Category.assoc] using
    congrArg
      (fun m => (integralComponentAt (nativeParameterGraphPoint X T U ψ t)).subschemeι ≫ m)
      (pullback.condition (f := (SmoothSite.product X T).hom)
        (g := (SmoothSite.product X U).hom)).symm

/-- The inverse exterior-support isomorphism preserves the actual support structure map. -/
theorem nativeMixedCoefficientChart_support_structure :
    (integralComponentAt (nativeExteriorPoint X Y U z hz)).subschemeι ≫
        pullback.fst (SmoothSite.product X U).hom (SmoothSite.product Y U).hom ≫
          (SmoothSite.product X U).hom =
      (nativeExteriorSupportIso X Y U z hz).inv ≫
        (exteriorIdentitySource X Y U (integralComponentAt z) ≫
          (SmoothSite.product X U).hom) := by
  simpa only [Category.assoc] using
    congrArg (fun m => m ≫ (SmoothSite.product X U).hom)
      (nativeExteriorSupportIso_inv_source X Y U z hz).symm

/-- The graph-component source map and the native exterior-support isomorphism give
an actual map from the support product into the literal coefficient scheme. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/GraphInterchangeGeometry.lean:144-181"
  "adaptation" "The actual native support-product chart; no generator model or flat parameter map"]
def nativeMixedCoefficientChart : nativeMixedGraphSupportProduct X Y T U ψ z hz t ⟶
    nativeMixedCoefficient X Y T U (integralComponentAt z) :=
  pullback.map
    ((integralComponentAt (nativeParameterGraphPoint X T U ψ t)).subschemeι ≫
      pullback.snd (SmoothSite.product X T).hom (SmoothSite.product X U).hom ≫
        (SmoothSite.product X U).hom)
    ((integralComponentAt (nativeExteriorPoint X Y U z hz)).subschemeι ≫
      pullback.fst (SmoothSite.product X U).hom (SmoothSite.product Y U).hom ≫
        (SmoothSite.product X U).hom)
    (SmoothSite.product X T).hom
    (exteriorIdentitySource X Y U (integralComponentAt z) ≫ (SmoothSite.product X U).hom)
    (nativeParameterGraphSource X T U ψ t)
    (nativeExteriorSupportIso X Y U z hz).inv (𝟙 (Spec (.of k)))
    ((Category.comp_id _).trans (nativeMixedCoefficientChart_source_structure X T U ψ t))
    ((Category.comp_id _).trans (nativeMixedCoefficientChart_support_structure X Y U z hz))

/-- Openness uses the graph component's source map, not its target map. -/
instance nativeMixedCoefficientChart_isOpenImmersion :
    IsOpenImmersion (nativeMixedCoefficientChart X Y T U ψ z hz t) := by
  unfold nativeMixedCoefficientChart
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    inferInstance inferInstance
    (nativeMixedCoefficientChart_source_structure X T U ψ t)
    (nativeMixedCoefficientChart_support_structure X Y U z hz)

@[reassoc (attr := simp)]
theorem nativeMixedCoefficientChart_fst :
    nativeMixedCoefficientChart X Y T U ψ z hz t ≫
      pullback.fst (pullback.fst X.hom T.hom ≫ X.hom)
        (exteriorIdentitySource X Y U (integralComponentAt z) ≫
          (pullback.fst X.hom U.hom ≫ X.hom)) =
      pullback.fst _ _ ≫ nativeParameterGraphSource X T U ψ t :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem nativeMixedCoefficientChart_snd :
    nativeMixedCoefficientChart X Y T U ψ z hz t ≫
      pullback.snd (pullback.fst X.hom T.hom ≫ X.hom)
        (exteriorIdentitySource X Y U (integralComponentAt z) ≫
          (pullback.fst X.hom U.hom ≫ X.hom)) =
      pullback.snd _ _ ≫ (nativeExteriorSupportIso X Y U z hz).inv :=
  pullback.lift_snd _ _ _

/-- The first original coordinate survives the open chart. -/
@[reassoc]
theorem nativeMixedCoefficientChart_first :
    nativeMixedCoefficientChart X Y T U ψ z hz t ≫ pullback.fst _ _ ≫
      pullback.fst X.hom T.hom =
    pullback.fst _ _ ≫ nativeParameterGraphSource X T U ψ t ≫
      pullback.fst X.hom T.hom :=
  nativeMixedCoefficientChart_fst_assoc X Y T U ψ z hz t _

/-- The parameter-source coordinate survives the open chart. -/
@[reassoc]
theorem nativeMixedCoefficientChart_second :
    nativeMixedCoefficientChart X Y T U ψ z hz t ≫ pullback.fst _ _ ≫
      pullback.snd X.hom T.hom =
    pullback.fst _ _ ≫ nativeParameterGraphSource X T U ψ t ≫
      pullback.snd X.hom T.hom :=
  nativeMixedCoefficientChart_fst_assoc X Y T U ψ z hz t _

/-- The original support coordinate survives the open chart. -/
@[reassoc]
theorem nativeMixedCoefficientChart_third :
    nativeMixedCoefficientChart X Y T U ψ z hz t ≫ pullback.snd _ _ ≫
      pullback.fst (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
        U.hom =
    pullback.snd _ _ ≫ (nativeExteriorSupportIso X Y U z hz).inv ≫
      pullback.fst (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
        U.hom :=
  nativeMixedCoefficientChart_snd_assoc X Y T U ψ z hz t _

/-- The parameter-target coordinate survives the open chart. -/
@[reassoc]
theorem nativeMixedCoefficientChart_fourth :
    nativeMixedCoefficientChart X Y T U ψ z hz t ≫ pullback.snd _ _ ≫
      pullback.snd (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
        U.hom =
    pullback.snd _ _ ≫ (nativeExteriorSupportIso X Y U z hz).inv ≫
      pullback.snd (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
        U.hom :=
  nativeMixedCoefficientChart_snd_assoc X Y T U ψ z hz t _

/-- The literal mixed pair agrees with the native ambient middle pair after the open chart. -/
@[reassoc, colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/GraphInterchangeGeometry.lean:215-250"
  "adaptation" "Exact middle-pair equality for the actual native graph component and \
    exterior support"]
theorem nativeMixedCoefficientChart_middlePair :
    nativeMixedCoefficientChart X Y T U ψ z hz t ≫
      nativeMixedCoefficientPair X Y T U (integralComponentAt z) ψ =
    correspondenceSupportProductInclusion (SmoothSite.product X T).hom
      (SmoothSite.product X U).hom (SmoothSite.product Y U).hom
      (nativeParameterGraphPoint X T U ψ t) (nativeExteriorPoint X Y U z hz) ≫
      correspondenceMiddlePair (SmoothSite.product X T).hom (SmoothSite.product X U).hom
        (SmoothSite.product Y U).hom := by
  have pairFst := nativeMixedCoefficientPair_fst X Y T U (integralComponentAt z) ψ
  change nativeMixedCoefficientPair X Y T U (integralComponentAt z) ψ ≫
    pullback.fst (SmoothSite.product X U).hom (SmoothSite.product X U).hom = _ at pairFst
  have pairSnd := nativeMixedCoefficientPair_snd X Y T U (integralComponentAt z) ψ
  change nativeMixedCoefficientPair X Y T U (integralComponentAt z) ψ ≫
    pullback.snd (SmoothSite.product X U).hom (SmoothSite.product X U).hom = _ at pairSnd
  have chartFst := nativeMixedCoefficientChart_fst_assoc X Y T U ψ z hz t
    (SmoothSite.productMap (𝟙 X) ψ).left
  change nativeMixedCoefficientChart X Y T U ψ z hz t ≫
    pullback.fst (SmoothSite.product X T).hom
      (exteriorIdentitySource X Y U (integralComponentAt z) ≫ (SmoothSite.product X U).hom) ≫
        (SmoothSite.productMap (𝟙 X) ψ).left = _ at chartFst
  have chartSnd := nativeMixedCoefficientChart_snd_assoc X Y T U ψ z hz t
    (exteriorIdentitySource X Y U (integralComponentAt z))
  change nativeMixedCoefficientChart X Y T U ψ z hz t ≫
    pullback.snd (SmoothSite.product X T).hom
      (exteriorIdentitySource X Y U (integralComponentAt z) ≫ (SmoothSite.product X U).hom) ≫
        exteriorIdentitySource X Y U (integralComponentAt z) = _ at chartSnd
  have hg := nativeGraphComponent_projection_graph (SmoothSite.product X T)
    (SmoothSite.product X U) (SmoothSite.productMap (𝟙 X) ψ) t
  change nativeParameterGraphSource X T U ψ t ≫ (SmoothSite.productMap (𝟙 X) ψ).left =
    (integralComponentAt (nativeParameterGraphPoint X T U ψ t)).subschemeι ≫
      pullback.snd (SmoothSite.product X T).hom (SmoothSite.product X U).hom at hg
  apply pullback.hom_ext
  · simp only [Category.assoc, pairFst,
      chartFst, correspondenceMiddlePair,
      pullback.map, pullback.lift_fst, correspondenceSupportProductInclusion_fst_assoc]
    simp only [nativeParameterGraphSource, Category.assoc] at hg
    rw [hg]
  · simp only [Category.assoc, pairSnd,
      chartSnd, nativeExteriorSupportIso_inv_source,
      correspondenceMiddlePair, pullback.map, pullback.lift_snd,
      correspondenceSupportProductInclusion_snd_assoc]

end Stacks.Chow

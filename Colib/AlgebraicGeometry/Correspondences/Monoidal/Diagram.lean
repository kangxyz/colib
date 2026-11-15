/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.IncidenceProduct

/-!
# The original incidence diagrams under exterior products

The isomorphism on the whole incidences and the permutation of the ambient
factors commute with their actual closed inclusions. These are scheme-map
identities, before passing to local rings or taking Tor. In particular they
supply the point equalities needed for the native stalk transports.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]

/-- The actual original ambient inclusion retains the selected incidence structure map. -/
@[reassoc]
theorem correspondenceIncidenceAmbientInclusion_base
    (X Y Z : SmoothSite (Spec (.of k)))
    (a : pullback (C := Scheme) X.hom Y.hom)
    (b : pullback (C := Scheme) Y.hom Z.hom) :
    correspondenceIncidenceAmbientInclusion X.hom Y.hom Z.hom a b ≫
      correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom =
        correspondenceIncidenceLeft X.hom Y.hom Z.hom a b ≫ X.hom := by
  calc
    _ = pullback.snd
        (exteriorSupportTargetProjection X Y (integralComponentAt a))
        (exteriorSupportSourceProjection Y Z (integralComponentAt b)) ≫
          exteriorSupportSourceProjection Y Z (integralComponentAt b) ≫ Y.hom := by
      simp only [correspondenceIncidenceAmbientInclusion,
        correspondenceIntersectionAmbientToField, Category.assoc,
        correspondenceTripleInclusion_snd_assoc, correspondenceIncidenceInclusion_snd_assoc,
        exteriorSupportSourceProjection]
    _ = pullback.fst
        (exteriorSupportTargetProjection X Y (integralComponentAt a))
        (exteriorSupportSourceProjection Y Z (integralComponentAt b)) ≫
          exteriorSupportTargetProjection X Y (integralComponentAt a) ≫ Y.hom := by
      rw [pullback.condition_assoc]
    _ = _ := (correspondenceIncidence_left_base_eq_middle a b).symm

variable (X Y Z U V W : SmoothSite (Spec (.of k)))
  (a : pullback (C := Scheme) X.hom Y.hom)
  (b : pullback (C := Scheme) Y.hom Z.hom)
  (c : pullback (C := Scheme) U.hom V.hom)
  (d : pullback (C := Scheme) V.hom W.hom)

local notation "A" => integralComponentAt a
local notation "B" => integralComponentAt b
local notation "C₀" => integralComponentAt c
local notation "D" => integralComponentAt d
local notation "sI" => correspondenceIncidenceLeft X.hom Y.hom Z.hom a b ≫ X.hom
local notation "sJ" => correspondenceIncidenceLeft U.hom V.hom W.hom c d ≫ U.hom
local notation "l" => correspondenceExteriorTarget X Y U V A C₀
local notation "r" => correspondenceExteriorSource Y Z V W B D
set_option quotPrecheck false in
local notation "f" => (SmoothSite.product X U).hom
set_option quotPrecheck false in
local notation "g" => (SmoothSite.product Y V).hom
set_option quotPrecheck false in
local notation "h" => (SmoothSite.product Z W).hom
local notation "e₁" => correspondenceExteriorInclusion X Y U V A C₀
local notation "e₂" => correspondenceExteriorInclusion Y Z V W B D

/-- The whole product-support incidence enters the native tensor triple product. -/
def correspondenceExteriorWholeIncidenceInclusion :
    correspondenceExteriorWholeIncidence X Y Z U V W a b c d ⟶
      correspondenceTripleProduct f g h :=
  pullback.map l r (pullback.snd f g) (pullback.fst g h) e₁ e₂
    (𝟙 (SmoothSite.product Y V).left) (by
      simpa only [Category.comp_id] using
        (correspondenceExteriorInclusion_snd X Y U V A C₀).symm) (by
      simpa only [Category.comp_id] using
        (correspondenceExteriorInclusion_fst Y Z V W B D).symm)

instance correspondenceExteriorWholeIncidenceInclusion_isClosedImmersion
    [IsFinite (exteriorSupportSourceProjection X Y A)]
    [IsFinite (exteriorSupportSourceProjection Y Z B)]
    [IsFinite (exteriorSupportSourceProjection U V C₀)]
    [IsFinite (exteriorSupportSourceProjection V W D)] :
    IsClosedImmersion (correspondenceExteriorWholeIncidenceInclusion X Y Z U V W a b c d) := by
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    inferInstance inferInstance (correspondenceExteriorInclusion_snd X Y U V A C₀).symm
      (correspondenceExteriorInclusion_fst Y Z V W B D).symm

/-- Its actual middle-diagonal inclusion in the tensor correspondence ambient. -/
abbrev correspondenceExteriorWholeIncidenceAmbientInclusion :
    correspondenceExteriorWholeIncidence X Y Z U V W a b c d ⟶
      correspondenceIntersectionAmbient f g h :=
  correspondenceExteriorWholeIncidenceInclusion X Y Z U V W a b c d ≫
    correspondenceTripleInclusion f g h

instance correspondenceExteriorWholeIncidenceAmbientInclusion_isClosedImmersion
    [IsFinite (exteriorSupportSourceProjection X Y A)]
    [IsFinite (exteriorSupportSourceProjection Y Z B)]
    [IsFinite (exteriorSupportSourceProjection U V C₀)]
    [IsFinite (exteriorSupportSourceProjection V W D)] :
    IsClosedImmersion
      (correspondenceExteriorWholeIncidenceAmbientInclusion X Y Z U V W a b c d) := by
  dsimp only [correspondenceExteriorWholeIncidenceAmbientInclusion]
  infer_instance

/-- The product of the two original incidence-ambient inclusions. -/
def correspondenceIncidenceProductAmbientMap :
    correspondenceIncidenceProduct X Y Z U V W a b c d ⟶
      correspondenceIntersectionAmbientProduct X Y Z U V W :=
  pullback.map sI sJ
    (correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom)
    (correspondenceIntersectionAmbientToField k U.hom V.hom W.hom)
    (correspondenceIncidenceAmbientInclusion X.hom Y.hom Z.hom a b)
    (correspondenceIncidenceAmbientInclusion U.hom V.hom W.hom c d) (𝟙 _) (by
      simpa only [Category.comp_id] using
        (correspondenceIncidenceAmbientInclusion_base X Y Z a b).symm) (by
      simpa only [Category.comp_id] using
        (correspondenceIncidenceAmbientInclusion_base U V W c d).symm)

instance correspondenceIncidenceProductAmbientMap_isClosedImmersion :
    IsClosedImmersion (correspondenceIncidenceProductAmbientMap X Y Z U V W a b c d) := by
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    inferInstance inferInstance (correspondenceIncidenceAmbientInclusion_base X Y Z a b).symm
      (correspondenceIncidenceAmbientInclusion_base U V W c d).symm

@[reassoc (attr := simp)]
theorem correspondenceIncidenceProductAmbientMap_fst :
    correspondenceIncidenceProductAmbientMap X Y Z U V W a b c d ≫
      pullback.fst (correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom)
        (correspondenceIntersectionAmbientToField k U.hom V.hom W.hom) =
      pullback.fst sI sJ ≫ correspondenceIncidenceAmbientInclusion X.hom Y.hom Z.hom a b :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correspondenceIncidenceProductAmbientMap_snd :
    correspondenceIncidenceProductAmbientMap X Y Z U V W a b c d ≫
      pullback.snd (correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom)
        (correspondenceIntersectionAmbientToField k U.hom V.hom W.hom) =
      pullback.snd sI sJ ≫ correspondenceIncidenceAmbientInclusion U.hom V.hom W.hom c d :=
  pullback.lift_snd _ _ _

/-- The two genuine incidence-ambient diagrams commute under the displayed permutations. -/
theorem correspondenceIncidenceProductIso_ambient :
    correspondenceIncidenceProductAmbientMap X Y Z U V W a b c d ≫
      (correspondenceIntersectionAmbientProductIso X Y Z U V W).hom =
      (correspondenceIncidenceProductIso X Y Z U V W a b c d).hom ≫
        correspondenceExteriorWholeIncidenceAmbientInclusion X Y Z U V W a b c d := by
  let e := correspondenceIntersectionAmbientProductIso X Y Z U V W
  have hfst : e.inv ≫
      pullback.fst (correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom)
        (correspondenceIntersectionAmbientToField k U.hom V.hom W.hom) =
      correspondenceIntersectionAmbientMap (SmoothSite.productFst X U)
        (SmoothSite.productFst Y V) (SmoothSite.productFst Z W) := by
    apply (cancel_epi e.hom).mp
    simpa only [Iso.hom_inv_id_assoc] using
      (correspondenceIntersectionAmbientProductIso_first X Y Z U V W).symm
  have hsnd : e.inv ≫
      pullback.snd (correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom)
        (correspondenceIntersectionAmbientToField k U.hom V.hom W.hom) =
      correspondenceIntersectionAmbientMap (SmoothSite.productSnd X U)
        (SmoothSite.productSnd Y V) (SmoothSite.productSnd Z W) := by
    apply (cancel_epi e.hom).mp
    simpa only [Iso.hom_inv_id_assoc] using
      (correspondenceIntersectionAmbientProductIso_second X Y Z U V W).symm
  apply (cancel_mono e.inv).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, hfst,
      correspondenceIntersectionAmbientProductIso_first,
      correspondenceIncidenceProductAmbientMap_fst]
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [correspondenceExteriorWholeIncidenceInclusion, correspondenceIntersectionAmbientMap,
        correspondenceIntersectionAmbientSmoothIso, pullback.congrHom_hom, pullback.map,
        correspondenceExteriorInclusion, correspondenceExteriorSource, correspondenceExteriorTarget,
        SmoothSite.productMap, SmoothSite.productLift, SmoothSite.productFst,
        SmoothSite.productSnd, Category.assoc, correspondenceIncidenceProductIso,
        correspondenceExteriorWholeIncidenceBaseIso, correspondenceExteriorTargetBaseIso,
        pullbackProductInterchangeIso, pullbackProductInterchangeHom]
  · simp only [Category.assoc, hsnd,
      correspondenceIntersectionAmbientProductIso_second,
      correspondenceIncidenceProductAmbientMap_snd]
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [correspondenceExteriorWholeIncidenceInclusion, correspondenceIntersectionAmbientMap,
        correspondenceIntersectionAmbientSmoothIso, pullback.congrHom_hom, pullback.map,
        correspondenceExteriorInclusion, correspondenceExteriorSource, correspondenceExteriorTarget,
        SmoothSite.productMap, SmoothSite.productLift, SmoothSite.productFst,
        SmoothSite.productSnd, Category.assoc, correspondenceIncidenceProductIso,
        correspondenceExteriorWholeIncidenceBaseIso, correspondenceExteriorTargetBaseIso,
        pullbackProductInterchangeIso, pullbackProductInterchangeHom]

end Stacks.Chow

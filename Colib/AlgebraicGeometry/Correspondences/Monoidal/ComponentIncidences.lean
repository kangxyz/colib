/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Components
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ProductResidueLength
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.KoszulDevissage
public import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward
import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDimension

/-!
# Incidences of the original product-support components

The native incidence of two product prime components embeds into the full
incidence of the two whole exterior supports. Its generic points map to
generic points of the whole incidence by finiteness and universal openness
over the first support.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

set_option backward.defeqAttrib.useBackward true

/-- The reduced closure of the image point, mapped back through the closed immersion. -/
def reducedClosureComponentInclusion {A B : Scheme.{u}} (i : A ⟶ B)
    [IsClosedImmersion i] (a : A) : (integralComponentAt (i a)).subscheme ⟶ A :=
  letI := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion i a
  inv (integralComponentMap i a) ≫ (integralComponentAt a).subschemeι

/-- Taking the two reduced point closures before or after closed immersions gives
isomorphic actual products. The map is induced by the native integral-component maps. -/
def reducedClosureComponentProductIso {A B C D S : Scheme.{u}}
    (i : A ⟶ B) (j : C ⟶ D) [IsClosedImmersion i] [IsClosedImmersion j]
    (f : A ⟶ S) (g : C ⟶ S) (a : A) (c : C) :
    pullback (reducedClosureComponentInclusion i a ≫ f)
      (reducedClosureComponentInclusion j c ≫ g) ≅
    pullback ((integralComponentAt a).subschemeι ≫ f)
      ((integralComponentAt c).subschemeι ≫ g) := by
  letI := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion i a
  letI := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion j c
  exact asIso (pullback.map
    (reducedClosureComponentInclusion i a ≫ f) (reducedClosureComponentInclusion j c ≫ g)
    ((integralComponentAt a).subschemeι ≫ f) ((integralComponentAt c).subschemeι ≫ g)
    (inv (integralComponentMap i a)) (inv (integralComponentMap j c)) (𝟙 S)
    (by simp only [reducedClosureComponentInclusion, Category.assoc, Category.comp_id])
    (by simp only [reducedClosureComponentInclusion, Category.assoc, Category.comp_id]))

/-- The product comparison commutes with its map to the whole product. -/
theorem reducedClosureComponentProductIso_hom_productClosedMap {A B C D S : Scheme.{u}}
    (i : A ⟶ B) (j : C ⟶ D) [IsClosedImmersion i] [IsClosedImmersion j]
    (f : A ⟶ S) (g : C ⟶ S) (a : A) (c : C) :
    (reducedClosureComponentProductIso i j f g a c).hom ≫
      Scheme.Hom.productClosedMap f g (integralComponentAt a).subschemeι
        (integralComponentAt c).subschemeι =
    Scheme.Hom.productClosedMap f g (reducedClosureComponentInclusion i a)
      (reducedClosureComponentInclusion j c) := by
  letI := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion i a
  letI := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion j c
  apply pullback.hom_ext
  · simp [reducedClosureComponentProductIso, Scheme.Hom.productClosedMap,
      reducedClosureComponentInclusion, pullback.map, Category.assoc]
  · simp [reducedClosureComponentProductIso, Scheme.Hom.productClosedMap,
      reducedClosureComponentInclusion, pullback.map, Category.assoc]

/-- The actual product comparison preserves local multiplicity, including nonreduced length. -/
theorem length_stalk_reducedClosureComponentProductIso {A B C D S : Scheme.{u}}
    (i : A ⟶ B) (j : C ⟶ D) [IsClosedImmersion i] [IsClosedImmersion j]
    (f : A ⟶ S) (g : C ⟶ S) (a : A) (c : C)
    (x : pullback (reducedClosureComponentInclusion i a ≫ f)
      (reducedClosureComponentInclusion j c ≫ g)) :
    let e := reducedClosureComponentProductIso i j f g a c
    Module.length ((pullback ((integralComponentAt a).subschemeι ≫ f)
      ((integralComponentAt c).subschemeι ≫ g)).presheaf.stalk (e.hom x))
      ((pullback ((integralComponentAt a).subschemeι ≫ f)
        ((integralComponentAt c).subschemeι ≫ g)).presheaf.stalk (e.hom x)) =
    Module.length ((pullback (reducedClosureComponentInclusion i a ≫ f)
      (reducedClosureComponentInclusion j c ≫ g)).presheaf.stalk x)
      ((pullback (reducedClosureComponentInclusion i a ≫ f)
        (reducedClosureComponentInclusion j c ≫ g)).presheaf.stalk x) := by
  dsimp only
  exact Module.length_eq_of_ringEquiv
    (asIso ((reducedClosureComponentProductIso i j f g a c).hom.stalkMap x)).commRingCatIsoToRingEquiv

private theorem reducedClosureComponentInclusion_comp {A B : Scheme.{u}} (i : A ⟶ B)
    [IsClosedImmersion i] (a : A) :
    reducedClosureComponentInclusion i a ≫ i = (integralComponentAt (i a)).subschemeι := by
  dsimp only [reducedClosureComponentInclusion]
  rw [Category.assoc, ← integralComponentMap_subschemeι, IsIso.inv_hom_id_assoc]

private theorem range_reducedClosureComponentInclusion {A B : Scheme.{u}} (i : A ⟶ B)
    [IsClosedImmersion i] (a : A) :
    Set.range (reducedClosureComponentInclusion i a) = closure ({a} : Set A) := by
  let := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion i a
  change Set.range ((integralComponentAt a).subschemeι ∘ inv (integralComponentMap i a)) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr (inv (integralComponentMap i a)).surjective,
    Set.image_univ, Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]

private instance reducedClosureComponentInclusion_isClosedImmersion {A B : Scheme.{u}}
    (i : A ⟶ B) [IsClosedImmersion i] (a : A) :
    IsClosedImmersion (reducedClosureComponentInclusion i a) := by
  let := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion i a
  dsimp only [reducedClosureComponentInclusion]
  infer_instance

private theorem reducedClosureComponentInclusion_genericPoint {A B : Scheme.{u}}
    (i : A ⟶ B) [IsClosedImmersion i] (a : A) :
    letI := isIntegral_integralComponentAt (i a)
    reducedClosureComponentInclusion i a
      (genericPoint (integralComponentAt (i a)).subscheme) = a := by
  let : IsIntegral (integralComponentAt (i a)).subscheme := isIntegral_integralComponentAt (i a)
  let : IsIntegral (integralComponentAt a).subscheme := isIntegral_integralComponentAt a
  let := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion i a
  change (integralComponentAt a).subschemeι
    (inv (integralComponentMap i a) (genericPoint (integralComponentAt (i a)).subscheme)) = a
  exact (congrArg (integralComponentAt a).subschemeι
    (genericPoint_eq_of_isOpenImmersion (inv (integralComponentMap i a)))).trans
      (genericPointOf_integralComponentAt a)

variable {k : Type u} [Field k] (X Y Z U V W : SmoothSite (Spec (.of k)))
  (a : pullback (C := Scheme) X.hom Y.hom)
  (b : pullback (C := Scheme) Y.hom Z.hom)
  (c : pullback (C := Scheme) U.hom V.hom)
  (d : pullback (C := Scheme) V.hom W.hom)
  (ha : IsFiniteCorrespondencePoint X.hom Y.hom a)
  (hb : IsFiniteCorrespondencePoint Y.hom Z.hom b)
  (hc : IsFiniteCorrespondencePoint U.hom V.hom c)
  (hd : IsFiniteCorrespondencePoint V.hom W.hom d)

local notation "D₁" =>
  correspondenceExteriorSupport (k := k) X Y U V (integralComponentAt a) (integralComponentAt c)
local notation "D₂" =>
  correspondenceExteriorSupport (k := k) Y Z V W (integralComponentAt b) (integralComponentAt d)
local notation "e₁" =>
  correspondenceExteriorInclusion (k := k) X Y U V (integralComponentAt a) (integralComponentAt c)
local notation "e₂" =>
  correspondenceExteriorInclusion (k := k) Y Z V W (integralComponentAt b) (integralComponentAt d)
local notation "l" =>
  correspondenceExteriorTarget (k := k) X Y U V (integralComponentAt a) (integralComponentAt c)
local notation "r" =>
  correspondenceExteriorSource (k := k) Y Z V W (integralComponentAt b) (integralComponentAt d)
local notation "H" => correspondenceExteriorWholeIncidence (k := k) X Y Z U V W a b c d
local notation "i" => correspondenceExteriorWholeIncidenceInclusion (k := k) X Y Z U V W a b c d
local notation "SupportProduct" =>
  correspondenceExteriorWholeSupportProduct (k := k) X Y Z U V W a b c d
local notation "q" => correspondenceExteriorWholeIncidenceToSupport (k := k) X Y Z U V W a b c d
local notation "kP" => correspondenceExteriorWholeSupportInclusion (k := k) X Y Z U V W a b c d
set_option quotPrecheck false in
local notation "f" => (SmoothSite.product X U).hom
set_option quotPrecheck false in
local notation "g" => (SmoothSite.product Y V).hom
set_option quotPrecheck false in
local notation "h" => (SmoothSite.product Z W).hom

variable
  (α : genericPoints (correspondenceExteriorSupport X Y U V
    (integralComponentAt a) (integralComponentAt c)))
  (β : genericPoints (correspondenceExteriorSupport Y Z V W
    (integralComponentAt b) (integralComponentAt d)))

/-- The point of the left ambient product defined by the selected support component. -/
abbrev leftComponentPoint :=
  correspondenceExteriorComponentPoint (k := k) X Y U V a c α

/-- The point of the right ambient product defined by the selected support component. -/
abbrev rightComponentPoint :=
  correspondenceExteriorComponentPoint (k := k) Y Z V W b d β

local notation "x" => leftComponentPoint X Y U V a c α
local notation "y" => rightComponentPoint Y Z V W b d β
set_option quotPrecheck false in
local notation "A" => (integralComponentAt x).subscheme
set_option quotPrecheck false in
local notation "B" => (integralComponentAt y).subscheme
set_option quotPrecheck false in
local notation "l'" => (integralComponentAt x).subschemeι ≫ pullback.snd f g
set_option quotPrecheck false in
local notation "r'" => (integralComponentAt y).subschemeι ≫ pullback.fst g h
set_option quotPrecheck false in
local notation "s₁" => (integralComponentAt x).subschemeι ≫ pullback.snd f g ≫ g
set_option quotPrecheck false in
local notation "s₂" => (integralComponentAt y).subschemeι ≫ pullback.fst g h ≫ g
local notation "L" => correspondenceIncidence f g h x y

include ha hc in
/-- The reduced left product component within the original whole left product. -/
def exteriorLeftComponentMap : A ⟶ D₁ := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  let inclusion :
      D₁ ⟶ pullback (C := Scheme) (SmoothSite.product X U).hom (SmoothSite.product Y V).hom :=
    e₁
  let : IsClosedImmersion inclusion :=
    inferInstanceAs (IsClosedImmersion e₁)
  exact reducedClosureComponentInclusion inclusion α.val

include hb hd in
/-- The reduced right product component within the original whole right product. -/
def exteriorRightComponentMap : B ⟶ D₂ := by
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  let inclusion :
      D₂ ⟶ pullback (C := Scheme) (SmoothSite.product Y V).hom (SmoothSite.product Z W).hom :=
    e₂
  let : IsClosedImmersion inclusion :=
    inferInstanceAs (IsClosedImmersion e₂)
  exact reducedClosureComponentInclusion inclusion β.val

local notation "u" => exteriorLeftComponentMap X Y U V a c ha hc α
local notation "v" => exteriorRightComponentMap Y Z V W b d hb hd β

@[reassoc (attr := simp)]
theorem exteriorLeftComponentMap_inclusion : u ≫ e₁ = (integralComponentAt x).subschemeι := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  exact reducedClosureComponentInclusion_comp e₁ α.val

@[reassoc (attr := simp)]
theorem exteriorRightComponentMap_inclusion : v ≫ e₂ = (integralComponentAt y).subschemeι := by
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  exact reducedClosureComponentInclusion_comp e₂ β.val

private theorem range_exteriorLeftComponentMap : Set.range u = closure ({α.val} : Set D₁) := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  exact range_reducedClosureComponentInclusion e₁ α.val

private theorem range_exteriorRightComponentMap : Set.range v = closure ({β.val} : Set D₂) := by
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  exact range_reducedClosureComponentInclusion e₂ β.val

instance exteriorLeftComponentMap_isClosedImmersion : IsClosedImmersion u := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  dsimp only [exteriorLeftComponentMap]
  infer_instance

instance exteriorRightComponentMap_isClosedImmersion : IsClosedImmersion v := by
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  dsimp only [exteriorRightComponentMap]
  infer_instance

theorem exteriorLeftComponentMap_target : u ≫ l = l' := by
  rw [← correspondenceExteriorInclusion_snd, exteriorLeftComponentMap_inclusion_assoc]

theorem exteriorRightComponentMap_source : v ≫ r = r' := by
  rw [← correspondenceExteriorInclusion_fst, exteriorRightComponentMap_inclusion_assoc]

/-- The native component-support product is the actual product of the two reduced
closures inside the whole exterior supports, not merely a scheme with the same support. -/
def exteriorComponentSupportReducedClosuresIso :
    correspondenceSupportProduct f g h x y ≅
      pullback ((integralComponentAt α.val).subschemeι ≫ l ≫ g)
        ((integralComponentAt β.val).subschemeι ≫ r ≫ g) := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  have hu : u ≫ l ≫ g = s₁ := by
    rw [← Category.assoc, exteriorLeftComponentMap_target]
    rfl
  have hv : v ≫ r ≫ g = s₂ := by
    rw [← Category.assoc, exteriorRightComponentMap_source]
    rfl
  exact pullback.congrHom hu.symm hv.symm ≪≫
    reducedClosureComponentProductIso e₁ e₂ (l ≫ g) (r ≫ g) α.val β.val

/-- The incidence of the two selected components maps to the whole incidence. -/
def exteriorComponentIncidenceMap : L ⟶ H :=
  pullback.map l' r' l r u v (𝟙 _)
    (by rw [Category.comp_id, exteriorLeftComponentMap_target])
    (by rw [Category.comp_id, exteriorRightComponentMap_source])

local notation "m" =>
  exteriorComponentIncidenceMap X Y Z U V W a b c d ha hb hc hd α β

/-- The product of the two selected reduced component supports in the whole support product. -/
def exteriorComponentSupportMap : correspondenceSupportProduct f g h x y ⟶ SupportProduct :=
  pullback.map s₁ s₂ (l ≫ g) (r ≫ g) u v (𝟙 (Spec (.of k)))
    ((Category.comp_id s₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g) (exteriorLeftComponentMap_target X Y U V a c ha hc α)).trans
        (Category.assoc _ _ _))).symm)
    ((Category.comp_id s₂).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g) (exteriorRightComponentMap_source Y Z V W b d hb hd β)).trans
        (Category.assoc _ _ _))).symm)

local notation "w" =>
  exteriorComponentSupportMap X Y Z U V W a b c d ha hb hc hd α β

set_option quotPrecheck false in
local notation "ClosureProduct" =>
  pullback ((integralComponentAt α.val).subschemeι ≫ l ≫ g)
    ((integralComponentAt β.val).subschemeι ≫ r ≫ g)

/-- The comparison of the native component product with the closure product lies over
the original whole support product. -/
theorem exteriorComponentSupportReducedClosuresIso_hom_productClosedMap :
    (exteriorComponentSupportReducedClosuresIso X Y Z U V W a b c d ha hb hc hd α β).hom ≫
      Scheme.Hom.productClosedMap (l ≫ g) (r ≫ g)
        (integralComponentAt α.val).subschemeι (integralComponentAt β.val).subschemeι = w := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  apply pullback.hom_ext
  · simp [exteriorComponentSupportReducedClosuresIso, reducedClosureComponentProductIso,
      Scheme.Hom.productClosedMap, exteriorComponentSupportMap, Iso.trans_hom, asIso_hom,
      pullback.congrHom_hom,
      pullback.map, exteriorLeftComponentMap, reducedClosureComponentInclusion, Category.assoc]
  · simp [exteriorComponentSupportReducedClosuresIso, reducedClosureComponentProductIso,
      Scheme.Hom.productClosedMap, exteriorComponentSupportMap, Iso.trans_hom, asIso_hom,
      pullback.congrHom_hom,
      pullback.map, exteriorRightComponentMap, reducedClosureComponentInclusion, Category.assoc]

/-- The exact comparison of component products retains the full local multiplicity. -/
theorem length_stalk_exteriorComponentSupportReducedClosuresIso
    (ξ : correspondenceSupportProduct f g h x y) :
    let e := exteriorComponentSupportReducedClosuresIso X Y Z U V W a b c d ha hb hc hd α β
    Module.length ((ClosureProduct).presheaf.stalk (e.hom ξ))
      ((ClosureProduct).presheaf.stalk (e.hom ξ)) =
    Module.length ((correspondenceSupportProduct f g h x y).presheaf.stalk ξ)
      ((correspondenceSupportProduct f g h x y).presheaf.stalk ξ) := by
  dsimp only
  exact Module.length_eq_of_ringEquiv
    (asIso ((exteriorComponentSupportReducedClosuresIso X Y Z U V W a b c d
      ha hb hc hd α β).hom.stalkMap ξ)).commRingCatIsoToRingEquiv

local instance closedImmersionStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (@IsClosedImmersion : MorphismProperty Scheme) :=
  (inferInstance : MorphismProperty.IsMultiplicative @IsClosedImmersion).toIsStableUnderComposition

instance exteriorComponentSupportMap_isClosedImmersion : IsClosedImmersion w := by
  dsimp only [exteriorComponentSupportMap]
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance
    (by rw [reassoc_of% exteriorLeftComponentMap_target])
    (by rw [reassoc_of% exteriorRightComponentMap_source])

@[reassoc]
theorem exteriorComponentSupportMap_fst :
    w ≫ pullback.fst (l ≫ g) (r ≫ g) = pullback.fst s₁ s₂ ≫ u :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem exteriorComponentSupportMap_snd :
    w ≫ pullback.snd (l ≫ g) (r ≫ g) = pullback.snd s₁ s₂ ≫ v :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem exteriorComponentIncidenceMap_fst :
    m ≫ pullback.fst l r = pullback.fst l' r' ≫ u :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem exteriorComponentIncidenceMap_snd :
    m ≫ pullback.snd l r = pullback.snd l' r' ≫ v :=
  pullback.lift_snd _ _ _

/-- Taking the support map after the component inclusion gives the native ambient map. -/
theorem exteriorComponentSupportMap_inclusion :
    w ≫ kP = correspondenceSupportProductInclusion f g h x y := by
  apply @pullback.hom_ext _ _ _ _ _ (pullback.snd f g ≫ g) (pullback.fst g h ≫ g)
  · have hh : kP ≫ pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) =
        pullback.fst (l ≫ g) (r ≫ g) ≫ e₁ := pullback.lift_fst _ _ _
    simp only [Category.assoc, hh, exteriorComponentSupportMap_fst_assoc,
      exteriorLeftComponentMap_inclusion, correspondenceSupportProductInclusion_fst]
  · have hh : kP ≫ pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) =
        pullback.snd (l ≫ g) (r ≫ g) ≫ e₂ := pullback.lift_snd _ _ _
    simp only [Category.assoc, hh, exteriorComponentSupportMap_snd_assoc,
      exteriorRightComponentMap_inclusion, correspondenceSupportProductInclusion_snd]

/-- The actual map from the component incidence to the support product agrees both ways. -/
theorem exteriorComponentIncidenceMap_support :
    m ≫ q = correspondenceIncidenceToSupportProduct f g h x y ≫ w := by
  apply @pullback.hom_ext _ _ _ _ _ (l ≫ g) (r ≫ g)
  · have hh : q ≫ pullback.fst (l ≫ g) (r ≫ g) = pullback.fst l r :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    simp only [Category.assoc, hh, exteriorComponentIncidenceMap_fst,
      exteriorComponentSupportMap_fst, correspondenceIncidenceToSupportProduct_fst_assoc]
  · have hh : q ≫ pullback.snd (l ≫ g) (r ≫ g) = pullback.snd l r :=
      (pullback.lift_snd _ _ _).trans (Category.comp_id _)
    simp only [Category.assoc, hh, exteriorComponentIncidenceMap_snd,
      exteriorComponentSupportMap_snd, correspondenceIncidenceToSupportProduct_snd_assoc]

instance exteriorComponentIncidenceMap_isClosedImmersion : IsClosedImmersion m :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance
    (exteriorLeftComponentMap_target X Y U V a c ha hc α).symm
    (exteriorRightComponentMap_source Y Z V W b d hb hd β).symm

/-- Both incidence maps agree in the actual native triple product. -/
@[reassoc]
theorem exteriorComponentIncidenceMap_inclusion :
    m ≫ i = correspondenceIncidenceInclusion f g h x y := by
  apply @pullback.hom_ext _ _ _ _ _ (pullback.snd f g) (pullback.fst g h)
  · have hh : i ≫ pullback.fst (pullback.snd f g) (pullback.fst g h) =
        pullback.fst l r ≫ e₁ := pullback.lift_fst _ _ _
    simp only [Category.assoc, hh, exteriorComponentIncidenceMap_fst_assoc,
      exteriorLeftComponentMap_inclusion, correspondenceIncidenceInclusion_fst]
  · have hh : i ≫ pullback.snd (pullback.snd f g) (pullback.fst g h) =
        pullback.snd l r ≫ e₂ := pullback.lift_snd _ _ _
    simp only [Category.assoc, hh, exteriorComponentIncidenceMap_snd_assoc,
      exteriorRightComponentMap_inclusion, correspondenceIncidenceInclusion_snd]

include hb hd in
theorem exteriorWholeIncidenceFst_finite :
    IsFinite (pullback.fst l r) := by
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  infer_instance

include hb hd in
theorem exteriorWholeIncidenceFst_open : UniversallyOpen (pullback.fst l r) := by
  let : UniversallyOpen (exteriorSupportSourceProjection Y Z (integralComponentAt b)) :=
    universallyOpen_finiteCorrespondenceProjection_of_smooth Y.hom Z.hom b hb
  let : UniversallyOpen (exteriorSupportSourceProjection V W (integralComponentAt d)) :=
    universallyOpen_finiteCorrespondenceProjection_of_smooth V.hom W.hom d hd
  infer_instance

/-- The native component incidence and the full incidence have compatible generics. -/
theorem exteriorComponentIncidenceMap_mem_genericPoints (z : genericPoints L) :
    m z.val ∈ genericPoints H := by
  let : IsFinite (pullback.fst l r) :=
    exteriorWholeIncidenceFst_finite X Y Z U V W a b c d hb hd
  let : IsLocallyNoetherian ((𝟭 Scheme).obj (SmoothSite.product Y V).left) :=
    SmoothSite.isLocallyNoetherian_overField k (SmoothSite.product Y V)
  let : IsNormal ((𝟭 Scheme).obj (SmoothSite.product Y V).left) :=
    SmoothSite.isNormal_overField k (SmoothSite.product Y V)
  have hβ := correspondenceExteriorComponentPoint_admissible (k := k) Y Z V W b d hb hd β
  have hz := mem_genericPoints_correspondenceIncidenceFst f g h x y hβ z.val z.property
  apply mem_genericPoints_of_isFinite_image (pullback.fst l r)
  have he := congrArg (fun t : L ⟶ D₁ => t z.val)
    (exteriorComponentIncidenceMap_fst X Y Z U V W a b c d ha hb hc hd α β)
  change (pullback.fst l r) (m z.val) = u (pullback.fst l' r' z.val) at he
  rw [he]
  let : IsIntegral A := isIntegral_integralComponentAt x
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  have heq : pullback.fst l' r' z.val = genericPoint A := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hz
  rw [heq, exteriorLeftComponentMap, reducedClosureComponentInclusion_genericPoint]
  exact α.property

/-- The original component-support image is the pair of inverse images of the two closures. -/
theorem range_exteriorComponentSupportMap :
    Set.range w =
      (pullback.fst (l ≫ g) (r ≫ g)) ⁻¹' closure ({α.val} : Set D₁) ∩
        (pullback.snd (l ≫ g) (r ≫ g)) ⁻¹' closure ({β.val} : Set D₂) := by
  let : Mono (𝟙 (Spec (.of k) : Scheme)) := inferInstance
  unfold exteriorComponentSupportMap
  rw [Scheme.Pullback.range_map s₁ s₂ (l ≫ g) (r ≫ g) u v (𝟙 (Spec (.of k))) _ _,
    range_exteriorLeftComponentMap,
    range_exteriorRightComponentMap]

/-- The point lifts to the component incidence precisely when its two support coordinates
belong to those components. -/
theorem range_exteriorComponentIncidenceMap :
    Set.range m =
      (pullback.fst l r) ⁻¹' closure ({α.val} : Set D₁) ∩
        (pullback.snd l r) ⁻¹' closure ({β.val} : Set D₂) := by
  unfold exteriorComponentIncidenceMap
  rw [Scheme.Pullback.range_map, range_exteriorLeftComponentMap,
    range_exteriorRightComponentMap]

section SupportGenerics

variable [PerfectField k]

include ha hc in
/-- Product-support generic multiplicities are one over a perfect field. -/
theorem correspondenceExteriorComponentWeight_eq_one :
    correspondenceExteriorComponentWeight (k := k) X Y U V a c α = 1 := by
  let : IsNoetherian D₁ := correspondenceExteriorSupport_isNoetherian (k := k) X Y U V a c ha hc
  let : IsIntegral (integralComponentAt a).subscheme := isIntegral_integralComponentAt a
  let : IsIntegral (integralComponentAt c).subscheme := isIntegral_integralComponentAt c
  let : IsReduced D₁ := isReduced_pullback_over_perfectField
    (exteriorSupportSourceProjection X Y (integralComponentAt a) ≫ X.hom)
    (exteriorSupportSourceProjection U V (integralComponentAt c) ≫ U.hom)
  exact (AlgebraicCycle.fundamentalCycle_apply_generic D₁ α).symm.trans
    (AlgebraicCycle.fundamentalCycle_apply_generic_of_isReduced D₁ α)

/-- A component's full support product is reduced over a perfect field. -/
theorem isReduced_exteriorComponentSupportProduct :
    IsReduced (correspondenceSupportProduct f g h x y) := by
  let : IsIntegral A := isIntegral_integralComponentAt x
  let : IsIntegral B := isIntegral_integralComponentAt y
  exact isReduced_pullback_over_perfectField
    ((integralComponentAt x).subschemeι ≫ pullback.snd f g ≫ g)
    ((integralComponentAt y).subschemeι ≫ pullback.fst g h ≫ g)

omit [PerfectField k] in
/-- The first projected label of an actual generic point of the whole support product. -/
def exteriorWholeSupportFirstGeneric (z : genericPoints SupportProduct) : genericPoints D₁ :=
  letI : Flat (r ≫ g) := inferInstanceAs (Flat (show _ ⟶ Spec (.of k) from r ≫ g))
  ⟨pullback.fst (l ≫ g) (r ≫ g) z.val, mem_genericPoints_of_flat _ z.property⟩

omit [PerfectField k] in
/-- The second projected label of a whole-support generic point. -/
def exteriorWholeSupportSecondGeneric (z : genericPoints SupportProduct) : genericPoints D₂ :=
  letI : Flat (l ≫ g) := inferInstanceAs (Flat (show _ ⟶ Spec (.of k) from l ≫ g))
  ⟨pullback.snd (l ≫ g) (r ≫ g) z.val, mem_genericPoints_of_flat _ z.property⟩

omit [PerfectField k] in
/-- Lifting a point to a component product uses exactly the two projected closed supports. -/
theorem exteriorComponentSupportMap_mem_range_iff (z : SupportProduct) :
    z ∈ Set.range w ↔
      α.val ⤳ pullback.fst (l ≫ g) (r ≫ g) z ∧
        β.val ⤳ pullback.snd (l ≫ g) (r ≫ g) z := by
  rw [range_exteriorComponentSupportMap]
  exact and_congr specializes_iff_mem_closure.symm specializes_iff_mem_closure.symm

end SupportGenerics

section SupportComponents

variable [PerfectField k]

omit [PerfectField k] in
private theorem exteriorComponentSupportMap_generic
    (t : genericPoints (correspondenceSupportProduct f g h x y)) :
    w t.val ∈ genericPoints SupportProduct := by
  let a₀ := pullback.fst (l ≫ g) (r ≫ g)
  let b₀ := pullback.snd (l ≫ g) (r ≫ g)
  let a₁ := pullback.fst s₁ s₂
  let b₁ := pullback.snd s₁ s₂
  let : Flat s₁ := inferInstanceAs (Flat (show _ ⟶ Spec (.of k) from s₁))
  let : Flat s₂ := inferInstanceAs (Flat (show _ ⟶ Spec (.of k) from s₂))
  have ha₁ : a₀ (w t.val) = u (a₁ t.val) := by
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun m' : correspondenceSupportProduct f g h x y ⟶ D₁ => m' t.val)
      (exteriorComponentSupportMap_fst X Y Z U V W a b c d ha hb hc hd α β)
  have hb₁ : b₀ (w t.val) = v (b₁ t.val) := by
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun m' : correspondenceSupportProduct f g h x y ⟶ D₂ => m' t.val)
      (exteriorComponentSupportMap_snd X Y Z U V W a b c d ha hb hc hd α β)
  let : IsIntegral A := isIntegral_integralComponentAt x
  let : IsIntegral B := isIntegral_integralComponentAt y
  have h₁ : a₁ t.val = genericPoint A := by
    have hg := mem_genericPoints_of_flat (pullback.fst s₁ s₂) t.property
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hg
  have h₂ : b₁ t.val = genericPoint B := by
    have hg := mem_genericPoints_of_flat (pullback.snd s₁ s₂) t.property
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hg
  have hu : u (genericPoint A) = α.val := by
    let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
    let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
    exact reducedClosureComponentInclusion_genericPoint e₁ α.val
  have hv : v (genericPoint B) = β.val := by
    let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
    let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
    exact reducedClosureComponentInclusion_genericPoint e₂ β.val
  rw [h₁, hu] at ha₁
  rw [h₂, hv] at hb₁
  apply mem_genericPoints_of_forall_specializes_eq
  intro y' hy'
  have hy₁ : a₀ y' = α.val :=
    forall_specializes_eq_of_mem_genericPoints α.property _
      (ha₁ ▸ hy'.map a₀.continuous)
  have hy₂ : b₀ y' = β.val :=
    forall_specializes_eq_of_mem_genericPoints β.property _
      (hb₁ ▸ hy'.map b₀.continuous)
  obtain ⟨z, rfl⟩ : y' ∈ Set.range w := by
    rw [exteriorComponentSupportMap_mem_range_iff]
    exact ⟨hy₁.symm ▸ specializes_rfl, hy₂.symm ▸ specializes_rfl⟩
  exact congrArg w (forall_specializes_eq_of_mem_genericPoints t.property z
    ((w).isClosedEmbedding.isInducing.specializes_iff.mp hy'))

omit [PerfectField k] in
/-- Lifting over a generic point of the whole support product gives a generic point upstairs. -/
theorem exteriorComponentSupportGeneric_iff (t : correspondenceSupportProduct f g h x y) :
    t ∈ genericPoints (correspondenceSupportProduct f g h x y) ↔
      w t ∈ genericPoints SupportProduct :=
  ⟨fun ht => exteriorComponentSupportMap_generic X Y Z U V W a b c d ha hb hc hd α β ⟨t, ht⟩,
    mem_genericPoints_of_isFinite_image w t⟩

omit [PerfectField k] in
/-- A finite closed product component contributes at each of its whole-support generics.
Conversely a whole-support generic belongs to the component product exactly when the two
original projected component labels agree. -/
theorem exteriorWholeSupportGeneric_component_iff (z : genericPoints SupportProduct) :
    z.val ∈ Set.range w ↔
      exteriorWholeSupportFirstGeneric X Y Z U V W a b c d z = α ∧
        exteriorWholeSupportSecondGeneric X Y Z U V W a b c d z = β := by
  rw [exteriorComponentSupportMap_mem_range_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨Subtype.ext (forall_specializes_eq_of_mem_genericPoints
      (exteriorWholeSupportFirstGeneric X Y Z U V W a b c d z).property _ h₁).symm,
      Subtype.ext (forall_specializes_eq_of_mem_genericPoints
        (exteriorWholeSupportSecondGeneric X Y Z U V W a b c d z).property _ h₂).symm⟩
  · rintro ⟨h₁, h₂⟩
    rw [← h₁, ← h₂]
    exact ⟨specializes_rfl, specializes_rfl⟩

private theorem isReduced_correspondenceExteriorWholeSupportProduct : IsReduced SupportProduct := by
  let : IsIntegral (integralComponentAt a).subscheme := isIntegral_integralComponentAt a
  let : IsIntegral (integralComponentAt b).subscheme := isIntegral_integralComponentAt b
  let : IsIntegral (integralComponentAt c).subscheme := isIntegral_integralComponentAt c
  let : IsIntegral (integralComponentAt d).subscheme := isIntegral_integralComponentAt d
  let : IsReduced D₁ := isReduced_pullback_over_perfectField
    (exteriorSupportSourceProjection X Y (integralComponentAt a) ≫ X.hom)
    (exteriorSupportSourceProjection U V (integralComponentAt c) ≫ U.hom)
  let : IsReduced D₂ := isReduced_pullback_over_perfectField
    (exteriorSupportSourceProjection Y Z (integralComponentAt b) ≫ Y.hom)
    (exteriorSupportSourceProjection V W (integralComponentAt d) ≫ V.hom)
  exact isReduced_pullback_over_perfectField (l ≫ g) (r ≫ g)

/-- The whole (possibly reducible) support product has one at every generic point. -/
theorem length_stalk_correspondenceExteriorWholeSupportProduct (t : genericPoints SupportProduct) :
    Module.length ((SupportProduct).presheaf.stalk t.val)
      ((SupportProduct).presheaf.stalk t.val) = 1 := by
  let : IsReduced SupportProduct :=
    isReduced_correspondenceExteriorWholeSupportProduct X Y Z U V W a b c d
  let := (isField_stalk_of_closure_mem_irreducibleComponents
    SupportProduct t.val t.property).toField
  exact Module.length_eq_one_iff.mpr inferInstance

omit [PerfectField k] in
/-- At a generic point of the selected component product its reduced closure, taken there or in
the whole support product, is the same closed subscheme of the whole support. -/
theorem exteriorComponentSupportMap_closureIso
    (t : genericPoints (correspondenceSupportProduct f g h x y)) :
    ∃ e : (integralComponentAt t.val).subscheme ≅ (integralComponentAt (w t.val)).subscheme,
      e.hom ≫ (integralComponentAt (w t.val)).subschemeι =
        (integralComponentAt t.val).subschemeι ≫ w := by
  let := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion w t.val
  exact ⟨asIso (integralComponentMap w t.val), integralComponentMap_subschemeι w t.val⟩

omit [PerfectField k] in
/-- At an actual generic component-product point, the whole-support multiplicity is
the product of the two input multiplicities and the full component-product multiplicity. -/
theorem length_stalk_exteriorWholeSupport_eq_mul_component
    (ξ : genericPoints (correspondenceSupportProduct f g h x y)) :
    Module.length ((SupportProduct).presheaf.stalk (w ξ.val))
      ((SupportProduct).presheaf.stalk (w ξ.val)) =
    Module.length ((D₁).presheaf.stalk α.val) ((D₁).presheaf.stalk α.val) *
      Module.length ((D₂).presheaf.stalk β.val) ((D₂).presheaf.stalk β.val) *
        Module.length ((correspondenceSupportProduct f g h x y).presheaf.stalk ξ.val)
          ((correspondenceSupportProduct f g h x y).presheaf.stalk ξ.val) := by
  let : IsNoetherian D₁ := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
  let : IsNoetherian D₂ := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
  have finiteGeneric (E : Scheme.{«u»}) [IsLocallyNoetherian E] (η : genericPoints E) :
      IsFiniteLength (E.presheaf.stalk η.val) (E.presheaf.stalk η.val) := by
    have hdim := ringKrullDim_stalk_eq_zero_of_mem_genericPoints (W := E) η
    let : Ring.KrullDimLE 0 (E.presheaf.stalk η.val) := by
      rw [Ring.krullDimLE_iff, hdim]
      rfl
    let : IsArtinianRing (E.presheaf.stalk η.val) :=
      isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩
    exact Module.length_ne_top_iff.mp (Module.length_ne_top (R := E.presheaf.stalk η.val))
  let η : genericPoints SupportProduct :=
    ⟨w ξ.val, exteriorComponentSupportMap_generic X Y Z U V W a b c d ha hb hc hd α β ξ⟩
  have hlabels := (exteriorWholeSupportGeneric_component_iff
    X Y Z U V W a b c d ha hb hc hd α β η).1 (Set.mem_range_self _)
  have hα : pullback.fst (l ≫ g) (r ≫ g) (w ξ.val) = α.val :=
    congrArg Subtype.val hlabels.1
  have hβ : pullback.snd (l ≫ g) (r ≫ g) (w ξ.val) = β.val :=
    congrArg Subtype.val hlabels.2
  let e := exteriorComponentSupportReducedClosuresIso X Y Z U V W a b c d ha hb hc hd α β
  let ζ : genericPoints ClosureProduct :=
    ⟨e.hom ξ.val, mem_genericPoints_of_flat e.hom ξ.property⟩
  have he : Scheme.Hom.productClosedMap (l ≫ g) (r ≫ g)
      (integralComponentAt α.val).subschemeι (integralComponentAt β.val).subschemeι ζ.val =
        w ξ.val := by
    exact congrArg (fun t => t ξ.val)
      (exteriorComponentSupportReducedClosuresIso_hom_productClosedMap
        X Y Z U V W a b c d ha hb hc hd α β)
  have H := length_stalk_product_at_generic_closures (l ≫ g) (r ≫ g) α β ζ
    (by rw [he]; exact hα) (by rw [he]; exact hβ) (finiteGeneric D₁ α) (finiteGeneric D₂ β)
  dsimp only at H
  rw [he, length_stalk_exteriorComponentSupportReducedClosuresIso
    X Y Z U V W a b c d ha hb hc hd α β ξ.val] at H
  exact H

end SupportComponents

end Stacks.Chow

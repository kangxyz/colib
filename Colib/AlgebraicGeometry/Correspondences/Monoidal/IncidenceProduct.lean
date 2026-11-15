/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Support
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ProductPullback
public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualTorCoefficients

/-!
# The whole incidence of two exterior support products

Before decomposing either product support into its generic components, its
incidence is canonically the product of the two original incidences. This
isomorphism retains all four support coordinates and the full scheme
structures. A Tor comparison is still needed to compare the cycles on them.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]
  (X Y Z U V W : SmoothSite (Spec (.of k)))
  (a : pullback (C := Scheme) X.hom Y.hom)
  (b : pullback (C := Scheme) Y.hom Z.hom)
  (c : pullback (C := Scheme) U.hom V.hom)
  (d : pullback (C := Scheme) V.hom W.hom)

local notation "A" => integralComponentAt a
local notation "B" => integralComponentAt b
local notation "C₀" => integralComponentAt c
local notation "D" => integralComponentAt d
local notation "f" => exteriorSupportTargetProjection X Y A
local notation "g" => exteriorSupportSourceProjection Y Z B
local notation "h" => exteriorSupportTargetProjection U V C₀
local notation "i" => exteriorSupportSourceProjection V W D
local notation "sI" => correspondenceIncidenceLeft X.hom Y.hom Z.hom a b ≫ X.hom
local notation "sJ" => correspondenceIncidenceLeft U.hom V.hom W.hom c d ≫ U.hom
local notation "sI'" => pullback.fst f g ≫ f ≫ Y.hom
local notation "sJ'" => pullback.fst h i ≫ h ≫ V.hom
local notation "l" => correspondenceExteriorTarget X Y U V A C₀
local notation "r" => correspondenceExteriorSource Y Z V W B D
local notation "l'" => pullbackProductFirstMap f h Y.hom V.hom
local notation "r'" => pullbackProductSecondMap g i Y.hom V.hom

/-- The incidence of the entire two product supports, before taking prime components. -/
abbrev correspondenceExteriorWholeIncidence : Scheme.{u} := pullback l r

/-- The product of the original two whole incidence schemes. -/
abbrev correspondenceIncidenceProduct : Scheme.{u} := pullback sI sJ

/-- A generic point of the product lies over an actual generic point of the first incidence. -/
def correspondenceIncidenceProductFirstGeneric
    (x : genericPoints (correspondenceIncidenceProduct X Y Z U V W a b c d)) :
    genericPoints (correspondenceIncidence X.hom Y.hom Z.hom a b) := by
  let : Flat sJ := inferInstanceAs
    (Flat (show correspondenceIncidence U.hom V.hom W.hom c d ⟶ Spec (.of k) from sJ))
  exact ⟨pullback.fst sI sJ x.val, mem_genericPoints_of_flat (pullback.fst sI sJ) x.property⟩

/-- The second projection likewise retains the original generic incidence label. -/
def correspondenceIncidenceProductSecondGeneric
    (x : genericPoints (correspondenceIncidenceProduct X Y Z U V W a b c d)) :
    genericPoints (correspondenceIncidence U.hom V.hom W.hom c d) := by
  let : Flat sI := inferInstanceAs
    (Flat (show correspondenceIncidence X.hom Y.hom Z.hom a b ⟶ Spec (.of k) from sI))
  exact ⟨pullback.snd sI sJ x.val, mem_genericPoints_of_flat (pullback.snd sI sJ) x.property⟩

/-- The source and middle coordinates give the identical structure map on an incidence. -/
theorem correspondenceIncidence_left_base_eq_middle {P Q R : SmoothSite (Spec (.of k))}
    (x : pullback (C := Scheme) P.hom Q.hom) (y : pullback (C := Scheme) Q.hom R.hom) :
    correspondenceIncidenceLeft P.hom Q.hom R.hom x y ≫ P.hom =
      pullback.fst
        (exteriorSupportTargetProjection P Q (integralComponentAt x))
        (exteriorSupportSourceProjection Q R (integralComponentAt y)) ≫
          exteriorSupportTargetProjection P Q (integralComponentAt x) ≫ Q.hom := by
  simpa only [correspondenceIncidenceLeft, exteriorSupportSourceProjection,
    exteriorSupportTargetProjection, Category.assoc] using
    congrArg (fun t => pullback.fst
      (exteriorSupportTargetProjection P Q (integralComponentAt x))
      (exteriorSupportSourceProjection Q R (integralComponentAt y)) ≫ t)
      (exteriorSupport_projection_base P Q (integralComponentAt x))

/-- Re-express the first product support using its target structure maps. -/
def correspondenceExteriorTargetBaseIso :
    correspondenceExteriorSupport X Y U V A C₀ ≅ pullback (f ≫ Y.hom) (h ≫ V.hom) :=
  pullback.congrHom (exteriorSupport_projection_base X Y A)
    (exteriorSupport_projection_base U V C₀)

/-- Changing the displayed structure maps preserves the actual product target map. -/
theorem correspondenceExteriorTargetBaseIso_inv_target :
    (correspondenceExteriorTargetBaseIso X Y U V a c).inv ≫ l = l' := by
  apply pullback.hom_ext <;>
    simp [correspondenceExteriorTargetBaseIso, pullback.map,
      correspondenceExteriorTarget, pullbackProductFirstMap, Category.assoc]

/-- The second support source is exactly the categorical product map. -/
theorem correspondenceExteriorSource_eq_productMap : r = r' := rfl

/-- The corresponding pullbacks have the same whole incidence after this base-map change. -/
def correspondenceExteriorWholeIncidenceBaseIso : pullback l' r' ≅
    correspondenceExteriorWholeIncidence X Y Z U V W a b c d := by
  let e := correspondenceExteriorTargetBaseIso X Y U V a c
  exact asIso (pullback.map l' r' l r e.inv (𝟙 _) (𝟙 _) (by
    simpa only [Category.comp_id] using
      (correspondenceExteriorTargetBaseIso_inv_target X Y U V a c).symm) (by
    simp only [Category.comp_id, Category.id_comp, correspondenceExteriorSource_eq_productMap]))

/-- The product of the original incidences is the whole incidence of their product supports. -/
def correspondenceIncidenceProductIso : correspondenceIncidenceProduct X Y Z U V W a b c d ≅
    correspondenceExteriorWholeIncidence X Y Z U V W a b c d :=
  pullback.congrHom (correspondenceIncidence_left_base_eq_middle a b)
    (correspondenceIncidence_left_base_eq_middle c d) ≪≫
      pullbackProductInterchangeIso f g h i Y.hom V.hom ≪≫
        correspondenceExteriorWholeIncidenceBaseIso X Y Z U V W a b c d

@[reassoc (attr := simp)]
theorem correspondenceIncidenceProductIso_hom_first :
    (correspondenceIncidenceProductIso X Y Z U V W a b c d).hom ≫ pullback.fst l r ≫
      pullback.fst (exteriorSupportSourceProjection X Y A ≫ X.hom)
        (exteriorSupportSourceProjection U V C₀ ≫ U.hom) =
      pullback.fst sI sJ ≫ pullback.fst f g := by
  simp [correspondenceIncidenceProductIso, correspondenceExteriorWholeIncidenceBaseIso,
    correspondenceExteriorTargetBaseIso, pullback.congrHom_hom, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem correspondenceIncidenceProductIso_hom_third :
    (correspondenceIncidenceProductIso X Y Z U V W a b c d).hom ≫ pullback.fst l r ≫
      pullback.snd (exteriorSupportSourceProjection X Y A ≫ X.hom)
        (exteriorSupportSourceProjection U V C₀ ≫ U.hom) =
      pullback.snd sI sJ ≫ pullback.fst h i := by
  simp [correspondenceIncidenceProductIso, correspondenceExteriorWholeIncidenceBaseIso,
    correspondenceExteriorTargetBaseIso, pullback.congrHom_hom, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem correspondenceIncidenceProductIso_hom_second :
    (correspondenceIncidenceProductIso X Y Z U V W a b c d).hom ≫ pullback.snd l r ≫
      pullback.fst (g ≫ Y.hom) (i ≫ V.hom) =
      pullback.fst sI sJ ≫ pullback.snd f g := by
  simp [correspondenceIncidenceProductIso, correspondenceExteriorWholeIncidenceBaseIso,
    pullback.congrHom_hom, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem correspondenceIncidenceProductIso_hom_fourth :
    (correspondenceIncidenceProductIso X Y Z U V W a b c d).hom ≫ pullback.snd l r ≫
      pullback.snd (g ≫ Y.hom) (i ≫ V.hom) =
      pullback.snd sI sJ ≫ pullback.snd h i := by
  simp [correspondenceIncidenceProductIso, correspondenceExteriorWholeIncidenceBaseIso,
    pullback.congrHom_hom, pullback.map, Category.assoc]

end Stacks.Chow

namespace Stacks.Chow

variable {k : Type u} [Field k]

/-- The existing four-factor ambient is the corresponding literal smooth-site product. -/
def correspondenceIntersectionAmbientSmoothIso (X Y Z : SmoothSite (Spec (.of k))) :
    correspondenceIntersectionAmbient X.hom Y.hom Z.hom ≅
      (SmoothSite.product (SmoothSite.product X Y) (SmoothSite.product Y Z)).left :=
  pullback.congrHom (pullback.condition (f := X.hom) (g := Y.hom)).symm rfl

@[reassoc]
theorem correspondenceIntersectionAmbientSmoothIso_base (X Y Z : SmoothSite (Spec (.of k))) :
    (correspondenceIntersectionAmbientSmoothIso X Y Z).hom ≫
      (SmoothSite.product (SmoothSite.product X Y) (SmoothSite.product Y Z)).hom =
        correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom := by
  simp [correspondenceIntersectionAmbientSmoothIso, pullback.congrHom_hom,
    pullback.map, SmoothSite.product_hom, correspondenceIntersectionAmbientToField,
    pullback.condition]

/-- The canonical map of the existing four-factor ambients induced by three smooth-site maps. -/
def correspondenceIntersectionAmbientMap
    {X Y Z X' Y' Z' : SmoothSite (Spec (.of k))}
    (a : X ⟶ X') (b : Y ⟶ Y') (c : Z ⟶ Z') :
    correspondenceIntersectionAmbient X.hom Y.hom Z.hom ⟶
      correspondenceIntersectionAmbient X'.hom Y'.hom Z'.hom :=
  (correspondenceIntersectionAmbientSmoothIso X Y Z).hom ≫
    (SmoothSite.productMap (SmoothSite.productMap a b) (SmoothSite.productMap b c)).left ≫
      (correspondenceIntersectionAmbientSmoothIso X' Y' Z').inv

/-- The product of the two original four-factor ambient schemes. -/
abbrev correspondenceIntersectionAmbientProduct (X Y Z U V W : SmoothSite (Spec (.of k))) :
    Scheme.{u} :=
  pullback (correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom)
    (correspondenceIntersectionAmbientToField k U.hom V.hom W.hom)

/-- The actual eight-factor permutation groups the two sources, middle factors and targets.
It is an isomorphism of schemes, before applying any stalk or cycle operation. -/
def correspondenceIntersectionAmbientProductIso (X Y Z U V W : SmoothSite (Spec (.of k))) :
    correspondenceIntersectionAmbientProduct X Y Z U V W ≅
      correspondenceIntersectionAmbient (SmoothSite.product X U).hom
        (SmoothSite.product Y V).hom (SmoothSite.product Z W).hom := by
  let e₁ := correspondenceIntersectionAmbientSmoothIso X Y Z
  let e₂ := correspondenceIntersectionAmbientSmoothIso U V W
  let A₁ := SmoothSite.product (SmoothSite.product X Y) (SmoothSite.product Y Z)
  let A₂ := SmoothSite.product (SmoothSite.product U V) (SmoothSite.product V W)
  let e₀ : correspondenceIntersectionAmbientProduct X Y Z U V W ≅
      (SmoothSite.product A₁ A₂).left :=
    asIso (pullback.map _ _ _ _ e₁.hom e₂.hom (𝟙 _) (by
      simpa only [Category.comp_id] using
        (correspondenceIntersectionAmbientSmoothIso_base X Y Z).symm) (by
      simpa only [Category.comp_id] using
        (correspondenceIntersectionAmbientSmoothIso_base U V W).symm))
  let e₃ := pullbackFourShuffleIso (SmoothSite.product X Y).hom
    (SmoothSite.product Y Z).hom (SmoothSite.product U V).hom (SmoothSite.product V W).hom
  let e₄ := pullbackFourShuffleIso X.hom Y.hom U.hom V.hom
  let e₅ := pullbackFourShuffleIso Y.hom Z.hom V.hom W.hom
  let B₁ := SmoothSite.product (SmoothSite.product X Y) (SmoothSite.product U V)
  let B₂ := SmoothSite.product (SmoothSite.product Y Z) (SmoothSite.product V W)
  let C₁ := SmoothSite.product (SmoothSite.product X U) (SmoothSite.product Y V)
  let C₂ := SmoothSite.product (SmoothSite.product Y V) (SmoothSite.product Z W)
  let e₆ : (SmoothSite.product B₁ B₂).left ≅ (SmoothSite.product C₁ C₂).left :=
    asIso (pullback.map B₁.hom B₂.hom C₁.hom C₂.hom e₄.hom e₅.hom (𝟙 _) (by
      simp [B₁, C₁, e₄, SmoothSite.product_hom]) (by
      simp [B₂, C₂, e₅, SmoothSite.product_hom]))
  exact e₀ ≪≫ e₃ ≪≫ e₆ ≪≫
    (correspondenceIntersectionAmbientSmoothIso
      (SmoothSite.product X U) (SmoothSite.product Y V) (SmoothSite.product Z W)).symm

/-- The ambient permutation followed by the first-factor maps is the original first projection. -/
@[reassoc (attr := simp)]
theorem correspondenceIntersectionAmbientProductIso_first
    (X Y Z U V W : SmoothSite (Spec (.of k))) :
    (correspondenceIntersectionAmbientProductIso X Y Z U V W).hom ≫
      correspondenceIntersectionAmbientMap (SmoothSite.productFst X U)
        (SmoothSite.productFst Y V) (SmoothSite.productFst Z W) =
      pullback.fst (correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom)
        (correspondenceIntersectionAmbientToField k U.hom V.hom W.hom) := by
  apply pullback.hom_ext <;> apply pullback.hom_ext <;>
    simp [correspondenceIntersectionAmbientProductIso, correspondenceIntersectionAmbientMap,
      correspondenceIntersectionAmbientSmoothIso, pullback.congrHom_hom, pullback.map,
      SmoothSite.productMap, SmoothSite.productLift, SmoothSite.productFst,
      SmoothSite.productSnd, Category.assoc]

/-- The ambient permutation likewise preserves the original second-factor projection. -/
@[reassoc (attr := simp)]
theorem correspondenceIntersectionAmbientProductIso_second
    (X Y Z U V W : SmoothSite (Spec (.of k))) :
    (correspondenceIntersectionAmbientProductIso X Y Z U V W).hom ≫
      correspondenceIntersectionAmbientMap (SmoothSite.productSnd X U)
        (SmoothSite.productSnd Y V) (SmoothSite.productSnd Z W) =
      pullback.snd (correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom)
        (correspondenceIntersectionAmbientToField k U.hom V.hom W.hom) := by
  apply pullback.hom_ext <;> apply pullback.hom_ext <;>
    simp [correspondenceIntersectionAmbientProductIso, correspondenceIntersectionAmbientMap,
      correspondenceIntersectionAmbientSmoothIso, pullback.congrHom_hom, pullback.map,
      SmoothSite.productMap, SmoothSite.productLift, SmoothSite.productFst,
      SmoothSite.productSnd, Category.assoc]

end Stacks.Chow

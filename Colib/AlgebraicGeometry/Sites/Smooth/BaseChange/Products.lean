/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.BaseChange
public import Colib.AlgebraicGeometry.Sites.Smooth.Products

/-! # Actual smooth-site products commute with arbitrary base change

The comparison and its universal property use the two original scheme
pullback projections. No smoothness or finite-degree assumption on the base
map is needed, and no substitute parameter object is chosen.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S T : Scheme.{u}} (r : T ⟶ S)
  {X Y : SmoothSite S} {Q : SmoothSite T}

/-- The original two scalar projections give the actual scalar-product lift. -/
def baseChangeProductLift (a : Q ⟶ (baseChange r).obj X)
    (b : Q ⟶ (baseChange r).obj Y) : Q ⟶ (baseChange r).obj (product X Y) := by
  have h (W : SmoothSite S) (s : Q ⟶ (baseChange r).obj W) :
      s.left ≫ pullback.fst W.hom r ≫ W.hom = Q.hom ≫ r := by
    rw [pullback.condition, ← Category.assoc]
    exact congrArg (fun f : Q.left ⟶ T => f ≫ r) (MorphismProperty.Over.w s)
  let l : Q.left ⟶ pullback X.hom Y.hom :=
    pullback.lift (a.left ≫ pullback.fst X.hom r) (b.left ≫ pullback.fst Y.hom r)
      (by simpa only [Category.assoc] using (h X a).trans (h Y b).symm)
  have hl : l ≫ (product X Y).hom = Q.hom ≫ r := by
    change l ≫ (pullback.fst X.hom Y.hom ≫ X.hom) = _
    rw [← Category.assoc, pullback.lift_fst, Category.assoc]
    exact h X a
  exact homMk (pullback.lift l Q.hom hl) (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)] theorem baseChangeProductLift_fst
    (a : Q ⟶ (baseChange r).obj X) (b : Q ⟶ (baseChange r).obj Y) :
    baseChangeProductLift r a b ≫ (baseChange r).map (productFst X Y) = a := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc, baseChange_map_fst,
      baseChangeProductLift, homMk_left, productFst, pullback.lift_fst_assoc,
      pullback.lift_fst]
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc, baseChange_map_snd,
      baseChangeProductLift, homMk_left, pullback.lift_snd]
    exact (MorphismProperty.Over.w a).symm

@[reassoc (attr := simp)] theorem baseChangeProductLift_snd
    (a : Q ⟶ (baseChange r).obj X) (b : Q ⟶ (baseChange r).obj Y) :
    baseChangeProductLift r a b ≫ (baseChange r).map (productSnd X Y) = b := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc, baseChange_map_fst,
      baseChangeProductLift, homMk_left, productSnd, pullback.lift_fst_assoc,
      pullback.lift_snd]
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc, baseChange_map_snd,
      baseChangeProductLift, homMk_left, pullback.lift_snd]
    exact (MorphismProperty.Over.w b).symm

/-- The two actual scalar projections determine every scalar-product map. -/
theorem baseChangeProduct_hom_ext {a b : Q ⟶ (baseChange r).obj (product X Y)}
    (h₁ : a ≫ (baseChange r).map (productFst X Y) =
      b ≫ (baseChange r).map (productFst X Y))
    (h₂ : a ≫ (baseChange r).map (productSnd X Y) =
      b ≫ (baseChange r).map (productSnd X Y)) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [MorphismProperty.Comma.comp_left, Category.assoc,
        baseChange_map_fst, productFst, homMk_left] using
        congrArg (fun f => f.left ≫ pullback.fst X.hom r) h₁
    · simpa only [MorphismProperty.Comma.comp_left, Category.assoc,
        baseChange_map_fst, productSnd, homMk_left] using
        congrArg (fun f => f.left ≫ pullback.fst Y.hom r) h₂
  · exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm

/-- The base-changed literal product has its original product universal property. -/
def baseChangeProductIsLimit (X Y : SmoothSite S) :
    IsLimit (BinaryFan.mk ((baseChange r).map (productFst X Y))
      ((baseChange r).map (productSnd X Y))) :=
  BinaryFan.isLimitMk (fun c => baseChangeProductLift r c.fst c.snd)
    (fun c => baseChangeProductLift_fst r c.fst c.snd)
    (fun c => baseChangeProductLift_snd r c.fst c.snd)
    (fun c _ h₁ h₂ => baseChangeProduct_hom_ext r
      (h₁.trans (baseChangeProductLift_fst r c.fst c.snd).symm)
      (h₂.trans (baseChangeProductLift_snd r c.fst c.snd).symm))

/-- Canonical actual-product base change, preserving both original projections. -/
def baseChangeProductIso (X Y : SmoothSite S) :
    (baseChange r).obj (product X Y) ≅
      product ((baseChange r).obj X) ((baseChange r).obj Y) :=
  IsLimit.conePointUniqueUpToIso (baseChangeProductIsLimit r X Y)
    (productIsLimit ((baseChange r).obj X) ((baseChange r).obj Y))

@[reassoc (attr := simp)] theorem baseChangeProductIso_fst (X Y : SmoothSite S) :
    (baseChangeProductIso r X Y).hom ≫
      productFst ((baseChange r).obj X) ((baseChange r).obj Y) =
        (baseChange r).map (productFst X Y) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)

@[reassoc (attr := simp)] theorem baseChangeProductIso_snd (X Y : SmoothSite S) :
    (baseChangeProductIso r X Y).hom ≫
      productSnd ((baseChange r).obj X) ((baseChange r).obj Y) =
        (baseChange r).map (productSnd X Y) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (⟨WalkingPair.right⟩ : Discrete WalkingPair)

/-- Natural in the two original factors, not merely in their isomorphism classes. -/
@[reassoc] theorem baseChangeProductIso_naturality
    {X' Y' : SmoothSite S} (f : X ⟶ X') (g : Y ⟶ Y') :
    (baseChange r).map (productMap f g) ≫ (baseChangeProductIso r X' Y').hom =
      (baseChangeProductIso r X Y).hom ≫
        productMap ((baseChange r).map f) ((baseChange r).map g) := by
  apply product_hom_ext <;>
    simp only [Category.assoc, baseChangeProductIso_fst, baseChangeProductIso_snd,
      baseChangeProductIso_fst_assoc, baseChangeProductIso_snd_assoc,
      productMap_fst, productMap_snd, ← Functor.map_comp,
      productMap_fst, productMap_snd]

/-- Actual base change of the base object is the new base via its second projection. -/
def baseChangeBaseIso : (baseChange r).obj (base S) ≅ base T :=
  MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 S) r)) (Category.comp_id _)

@[simp] theorem baseChangeBaseIso_hom_left :
    (baseChangeBaseIso r).hom.left = pullback.snd (𝟙 S) r := rfl

end AlgebraicGeometry.Scheme.SmoothSite

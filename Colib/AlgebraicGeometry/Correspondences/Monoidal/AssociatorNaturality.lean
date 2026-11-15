/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Components
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ConstraintNaturality
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.GraphTransport
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.FiniteExteriorPushforward
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ProductFundamental
import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward
import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity

/-!
# The canonical association of three correspondence supports

The two whole supports are the two associations of the products of the
same three reduced point closures. The two source and two target
associators carry the original inclusion across that identification.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]
  (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : SmoothSite (Spec (.of k)))
  (I : (pullback X₁.hom X₂.hom).IdealSheafData)
  (J : (pullback Y₁.hom Y₂.hom).IdealSheafData)
  (K : (pullback Z₁.hom Z₂.hom).IdealSheafData)

local notation "a₀" => exteriorSupportSourceProjection X₁ X₂ I ≫ X₁.hom
local notation "b₀" => exteriorSupportSourceProjection Y₁ Y₂ J ≫ Y₁.hom
local notation "c₀" => exteriorSupportSourceProjection Z₁ Z₂ K ≫ Z₁.hom
local notation "X" => SmoothSite.product

/-- The original exterior support inclusion lies over the first support's structure map. -/
theorem correspondenceExteriorInclusion_comp_base
    (A B C D : SmoothSite (Spec (.of k)))
    (P : (pullback A.hom B.hom).IdealSheafData)
    (Q : (pullback C.hom D.hom).IdealSheafData) :
    correspondenceExteriorInclusion A B C D P Q ≫ pullback.fst (X A C).hom (X B D).hom ≫
        (X A C).hom =
      pullback.fst (exteriorSupportSourceProjection A B P ≫ A.hom)
        (exteriorSupportSourceProjection C D Q ≫ C.hom) ≫ exteriorSupportSourceProjection A B P ≫
          A.hom := by
  rw [correspondenceExteriorInclusion_fst_assoc]
  change correspondenceExteriorSource A B C D P Q ≫ pullback.fst A.hom C.hom ≫ A.hom = _
  rw [correspondenceExteriorSource_fst_assoc]
  rfl

/-- The original left-associated ambient map of the three given supports. -/
def leftExteriorSupportMap :
    pullback (pullback.fst a₀ b₀ ≫ a₀) c₀ ⟶
      pullback (X (X X₁ Y₁) Z₁).hom (X (X X₂ Y₂) Z₂).hom :=
  let f := correspondenceExteriorInclusion X₁ X₂ Y₁ Y₂ I J
  let i := IdealSheafData.subschemeι K
  let e := correspondenceExteriorShuffle (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂
  pullback.map _ _ _ _ f i (𝟙 (Spec (.of k)))
    ((Category.comp_id (pullback.fst a₀ b₀ ≫ a₀)).trans
      (correspondenceExteriorInclusion_comp_base X₁ X₂ Y₁ Y₂ I J).symm)
    ((Category.comp_id c₀).trans (Category.assoc K.subschemeι
      (pullback.fst Z₁.hom Z₂.hom) Z₁.hom)) ≫ e.hom

/-- The original right-associated ambient map of the three given supports. -/
def rightExteriorSupportMap :
    pullback a₀ (pullback.fst b₀ c₀ ≫ b₀) ⟶
      pullback (X X₁ (X Y₁ Z₁)).hom (X X₂ (X Y₂ Z₂)).hom :=
  let f := correspondenceExteriorInclusion Y₁ Y₂ Z₁ Z₂ J K
  let i := IdealSheafData.subschemeι I
  let e := correspondenceExteriorShuffle X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂)
  pullback.map _ _ _ _ i f (𝟙 (Spec (.of k)))
    ((Category.comp_id a₀).trans (Category.assoc I.subschemeι
      (pullback.fst X₁.hom X₂.hom) X₁.hom))
    ((Category.comp_id (pullback.fst b₀ c₀ ≫ b₀)).trans
      (correspondenceExteriorInclusion_comp_base Y₁ Y₂ Z₁ Z₂ J K).symm) ≫ e.hom

instance [IsFinite (exteriorSupportSourceProjection X₁ X₂ I)]
    [IsFinite (exteriorSupportSourceProjection Y₁ Y₂ J)] :
    IsFinite (leftExteriorSupportMap X₁ X₂ Y₁ Y₂ Z₁ Z₂ I J K) := by
  unfold leftExteriorSupportMap
  dsimp only
  exact MorphismProperty.comp_mem (@IsFinite) _ _
    (MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance
      (correspondenceExteriorInclusion_comp_base X₁ X₂ Y₁ Y₂ I J).symm
      (Category.assoc K.subschemeι (pullback.fst Z₁.hom Z₂.hom) Z₁.hom)) inferInstance

instance [IsFinite (exteriorSupportSourceProjection Y₁ Y₂ J)]
    [IsFinite (exteriorSupportSourceProjection Z₁ Z₂ K)] :
    IsFinite (rightExteriorSupportMap X₁ X₂ Y₁ Y₂ Z₁ Z₂ I J K) := by
  unfold rightExteriorSupportMap
  dsimp only
  exact MorphismProperty.comp_mem (@IsFinite) _ _
    (MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance
      (Category.assoc I.subschemeι (pullback.fst X₁.hom X₂.hom) X₁.hom)
      (correspondenceExteriorInclusion_comp_base Y₁ Y₂ Z₁ Z₂ J K).symm) inferInstance

private theorem smoothAssociator_fst (U V W : SmoothSite (Spec (.of k))) :
    (α_ U V W).hom ≫ SmoothSite.productFst U (X V W) =
      SmoothSite.productFst (X U V) W ≫ SmoothSite.productFst U V :=
  CartesianMonoidalCategory.associator_hom_fst U V W

private theorem smoothAssociator_snd_fst (U V W : SmoothSite (Spec (.of k))) :
    (α_ U V W).hom ≫ SmoothSite.productSnd U (X V W) ≫ SmoothSite.productFst V W =
      SmoothSite.productFst (X U V) W ≫ SmoothSite.productSnd U V :=
  CartesianMonoidalCategory.associator_hom_snd_fst U V W

private theorem smoothAssociator_snd_snd (U V W : SmoothSite (Spec (.of k))) :
    (α_ U V W).hom ≫ SmoothSite.productSnd U (X V W) ≫ SmoothSite.productSnd V W =
      SmoothSite.productSnd (X U V) W :=
  CartesianMonoidalCategory.associator_hom_snd_snd U V W

private theorem exteriorAssociator_ambient_projection₁
    (U V W U' V' W' : SmoothSite (Spec (.of k))) :
    (SmoothSite.productMap (α_ U V W).hom (α_ U' V' W').hom).left ≫
      pullback.fst (X U (X V W)).hom (X U' (X V' W')).hom =
    pullback.fst (X (X U V) W).hom (X (X U' V') W').hom ≫ (α_ U V W).hom.left :=
  congrArg (fun f => f.left) (SmoothSite.productMap_fst (α_ U V W).hom (α_ U' V' W').hom)

private theorem exteriorAssociator_ambient_projection₂
    (U V W U' V' W' : SmoothSite (Spec (.of k))) :
    (SmoothSite.productMap (α_ U V W).hom (α_ U' V' W').hom).left ≫
      pullback.snd (X U (X V W)).hom (X U' (X V' W')).hom =
    pullback.snd (X (X U V) W).hom (X (X U' V') W').hom ≫ (α_ U' V' W').hom.left :=
  congrArg (fun f => f.left) (SmoothSite.productMap_snd (α_ U V W).hom (α_ U' V' W').hom)

private theorem shuffle_fst_fst (A B C D : SmoothSite (Spec (.of k))) :
    (correspondenceExteriorShuffle A B C D).hom ≫
        pullback.fst (X A C).hom (X B D).hom ≫ pullback.fst A.hom C.hom =
      pullback.fst (pullback.fst A.hom B.hom ≫ A.hom) (pullback.fst C.hom D.hom ≫ C.hom) ≫
        pullback.fst A.hom B.hom :=
  pullbackFourShuffleIso_hom_fst_fst A.hom B.hom C.hom D.hom

private theorem shuffle_fst_snd (A B C D : SmoothSite (Spec (.of k))) :
    (correspondenceExteriorShuffle A B C D).hom ≫
        pullback.fst (X A C).hom (X B D).hom ≫ pullback.snd A.hom C.hom =
      pullback.snd (pullback.fst A.hom B.hom ≫ A.hom) (pullback.fst C.hom D.hom ≫ C.hom) ≫
        pullback.fst C.hom D.hom :=
  pullbackFourShuffleIso_hom_fst_snd A.hom B.hom C.hom D.hom

private theorem shuffle_snd_fst (A B C D : SmoothSite (Spec (.of k))) :
    (correspondenceExteriorShuffle A B C D).hom ≫
        pullback.snd (X A C).hom (X B D).hom ≫ pullback.fst B.hom D.hom =
      pullback.fst (pullback.fst A.hom B.hom ≫ A.hom) (pullback.fst C.hom D.hom ≫ C.hom) ≫
        pullback.snd A.hom B.hom :=
  pullbackFourShuffleIso_hom_snd_fst A.hom B.hom C.hom D.hom

private theorem shuffle_snd_snd (A B C D : SmoothSite (Spec (.of k))) :
    (correspondenceExteriorShuffle A B C D).hom ≫
        pullback.snd (X A C).hom (X B D).hom ≫ pullback.snd B.hom D.hom =
      pullback.snd (pullback.fst A.hom B.hom ≫ A.hom) (pullback.fst C.hom D.hom ≫ C.hom) ≫
        pullback.snd C.hom D.hom :=
  pullbackFourShuffleIso_hom_snd_snd A.hom B.hom C.hom D.hom

private theorem inclusion_fst_fst (A B C D : SmoothSite (Spec (.of k)))
    (P : (pullback A.hom B.hom).IdealSheafData) (Q : (pullback C.hom D.hom).IdealSheafData) :
    correspondenceExteriorInclusion A B C D P Q ≫
        pullback.fst (pullback.fst A.hom C.hom ≫ A.hom) (pullback.fst B.hom D.hom ≫ B.hom) ≫
        pullback.fst A.hom C.hom =
      pullback.fst (exteriorSupportSourceProjection A B P ≫ A.hom)
        (exteriorSupportSourceProjection C D Q ≫ C.hom) ≫
        exteriorSupportSourceProjection A B P := by
  change correspondenceExteriorInclusion A B C D P Q ≫
      pullback.fst (X A C).hom (X B D).hom ≫ pullback.fst A.hom C.hom = _
  rw [correspondenceExteriorInclusion_fst_assoc, correspondenceExteriorSource_fst]

private theorem inclusion_fst_snd (A B C D : SmoothSite (Spec (.of k)))
    (P : (pullback A.hom B.hom).IdealSheafData) (Q : (pullback C.hom D.hom).IdealSheafData) :
    correspondenceExteriorInclusion A B C D P Q ≫
        pullback.fst (pullback.fst A.hom C.hom ≫ A.hom) (pullback.fst B.hom D.hom ≫ B.hom) ≫
        pullback.snd A.hom C.hom =
      pullback.snd (exteriorSupportSourceProjection A B P ≫ A.hom)
        (exteriorSupportSourceProjection C D Q ≫ C.hom) ≫
        exteriorSupportSourceProjection C D Q := by
  change correspondenceExteriorInclusion A B C D P Q ≫
      pullback.fst (X A C).hom (X B D).hom ≫ pullback.snd A.hom C.hom = _
  rw [correspondenceExteriorInclusion_fst_assoc, correspondenceExteriorSource_snd]

private theorem inclusion_snd_fst (A B C D : SmoothSite (Spec (.of k)))
    (P : (pullback A.hom B.hom).IdealSheafData) (Q : (pullback C.hom D.hom).IdealSheafData) :
    correspondenceExteriorInclusion A B C D P Q ≫
        pullback.snd (pullback.fst A.hom C.hom ≫ A.hom) (pullback.fst B.hom D.hom ≫ B.hom) ≫
        pullback.fst B.hom D.hom =
      pullback.fst (exteriorSupportSourceProjection A B P ≫ A.hom)
        (exteriorSupportSourceProjection C D Q ≫ C.hom) ≫
        exteriorSupportTargetProjection A B P := by
  change correspondenceExteriorInclusion A B C D P Q ≫
      pullback.snd (X A C).hom (X B D).hom ≫ pullback.fst B.hom D.hom = _
  rw [correspondenceExteriorInclusion_snd_assoc, correspondenceExteriorTarget_fst]

private theorem inclusion_snd_snd (A B C D : SmoothSite (Spec (.of k)))
    (P : (pullback A.hom B.hom).IdealSheafData) (Q : (pullback C.hom D.hom).IdealSheafData) :
    correspondenceExteriorInclusion A B C D P Q ≫
        pullback.snd (pullback.fst A.hom C.hom ≫ A.hom) (pullback.fst B.hom D.hom ≫ B.hom) ≫
        pullback.snd B.hom D.hom =
      pullback.snd (exteriorSupportSourceProjection A B P ≫ A.hom)
        (exteriorSupportSourceProjection C D Q ≫ C.hom) ≫
        exteriorSupportTargetProjection C D Q := by
  change correspondenceExteriorInclusion A B C D P Q ≫
      pullback.snd (X A C).hom (X B D).hom ≫ pullback.snd B.hom D.hom = _
  rw [correspondenceExteriorInclusion_snd_assoc, correspondenceExteriorTarget_snd]

/-- The scheme associators identify the two original maps of the same triple support. -/
theorem leftExteriorSupportMap_comp_associators :
    leftExteriorSupportMap X₁ X₂ Y₁ Y₂ Z₁ Z₂ I J K ≫
        (SmoothSite.productMap (α_ X₁ Y₁ Z₁).hom (α_ X₂ Y₂ Z₂).hom).left =
      (tripleProductAssoc a₀ b₀ c₀).hom ≫ rightExteriorSupportMap X₁ X₂ Y₁ Y₂ Z₁ Z₂ I J K := by
  let E := leftExteriorSupportMap X₁ X₂ Y₁ Y₂ Z₁ Z₂ I J K
  have h₁ := exteriorAssociator_ambient_projection₁ X₁ Y₁ Z₁ X₂ Y₂ Z₂
  have h₂ := exteriorAssociator_ambient_projection₂ X₁ Y₁ Z₁ X₂ Y₂ Z₂
  have hX₁ : (α_ X₁ Y₁ Z₁).hom.left ≫ pullback.fst X₁.hom (X Y₁ Z₁).hom =
      pullback.fst (X X₁ Y₁).hom Z₁.hom ≫ pullback.fst X₁.hom Y₁.hom :=
    congrArg (fun f => f.left) (smoothAssociator_fst X₁ Y₁ Z₁)
  have hY₁ : (α_ X₁ Y₁ Z₁).hom.left ≫
      pullback.snd X₁.hom (X Y₁ Z₁).hom ≫ pullback.fst Y₁.hom Z₁.hom =
      pullback.fst (X X₁ Y₁).hom Z₁.hom ≫ pullback.snd X₁.hom Y₁.hom :=
    congrArg (fun f => f.left) (smoothAssociator_snd_fst X₁ Y₁ Z₁)
  have hZ₁ : (α_ X₁ Y₁ Z₁).hom.left ≫
      pullback.snd X₁.hom (X Y₁ Z₁).hom ≫ pullback.snd Y₁.hom Z₁.hom =
      pullback.snd (X X₁ Y₁).hom Z₁.hom :=
    congrArg (fun f => f.left) (smoothAssociator_snd_snd X₁ Y₁ Z₁)
  have hX₂ : (α_ X₂ Y₂ Z₂).hom.left ≫ pullback.fst X₂.hom (X Y₂ Z₂).hom =
      pullback.fst (X X₂ Y₂).hom Z₂.hom ≫ pullback.fst X₂.hom Y₂.hom :=
    congrArg (fun f => f.left) (smoothAssociator_fst X₂ Y₂ Z₂)
  have hY₂ : (α_ X₂ Y₂ Z₂).hom.left ≫
      pullback.snd X₂.hom (X Y₂ Z₂).hom ≫ pullback.fst Y₂.hom Z₂.hom =
      pullback.fst (X X₂ Y₂).hom Z₂.hom ≫ pullback.snd X₂.hom Y₂.hom :=
    congrArg (fun f => f.left) (smoothAssociator_snd_fst X₂ Y₂ Z₂)
  have hZ₂ : (α_ X₂ Y₂ Z₂).hom.left ≫
      pullback.snd X₂.hom (X Y₂ Z₂).hom ≫ pullback.snd Y₂.hom Z₂.hom =
      pullback.snd (X X₂ Y₂).hom Z₂.hom :=
    congrArg (fun f => f.left) (smoothAssociator_snd_snd X₂ Y₂ Z₂)
  have ht₁ := tripleProductAssoc_hom_fst a₀ b₀ c₀
  have ht₂ := tripleProductAssoc_hom_snd_fst a₀ b₀ c₀
  have ht₃ := tripleProductAssoc_hom_snd_snd a₀ b₀ c₀
  apply pullback.hom_ext (f := (X X₁ (X Y₁ Z₁)).hom) (g := (X X₂ (X Y₂ Z₂)).hom)
  · change (E ≫ _) ≫ pullback.fst (X X₁ (X Y₁ Z₁)).hom (X X₂ (X Y₂ Z₂)).hom = _
    refine ((Category.assoc E _ _).trans (congrArg (E ≫ ·) h₁)).trans ?_
    apply pullback.hom_ext (f := X₁.hom) (g := (X Y₁ Z₁).hom)
    · simp only [Category.assoc, hX₁, E, leftExteriorSupportMap, rightExteriorSupportMap,
        reassoc_of% (shuffle_fst_fst (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂),
        shuffle_fst_fst X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂)]
      simp only [SmoothSite.product_left, SmoothSite.product_hom, pullback.map,
        pullback.lift_fst_assoc, reassoc_of% ht₁, inclusion_fst_fst X₁ X₂ Y₁ Y₂ I J,
        Category.assoc]
    · apply pullback.hom_ext (f := Y₁.hom) (g := Z₁.hom)
      · simp only [Category.assoc, hY₁, E, leftExteriorSupportMap, rightExteriorSupportMap,
          reassoc_of% (shuffle_fst_fst (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂),
          reassoc_of% (shuffle_fst_snd X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂))]
        simp only [SmoothSite.product_left, SmoothSite.product_hom, pullback.map,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc, reassoc_of% ht₂,
          inclusion_fst_snd X₁ X₂ Y₁ Y₂ I J,
          inclusion_fst_fst Y₁ Y₂ Z₁ Z₂ J K,
        Category.assoc]
      · simp only [Category.assoc, hZ₁, E, leftExteriorSupportMap, rightExteriorSupportMap,
          shuffle_fst_snd (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂,
          reassoc_of% (shuffle_fst_snd X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂))]
        simp only [SmoothSite.product_left, SmoothSite.product_hom, pullback.map,
          pullback.lift_snd_assoc, reassoc_of% ht₃, inclusion_fst_snd Y₁ Y₂ Z₁ Z₂ J K,
        Category.assoc]
  · change (E ≫ _) ≫ pullback.snd (X X₁ (X Y₁ Z₁)).hom (X X₂ (X Y₂ Z₂)).hom = _
    refine ((Category.assoc E _ _).trans (congrArg (E ≫ ·) h₂)).trans ?_
    apply pullback.hom_ext (f := X₂.hom) (g := (X Y₂ Z₂).hom)
    · simp only [Category.assoc, hX₂, E, leftExteriorSupportMap, rightExteriorSupportMap,
        reassoc_of% (shuffle_snd_fst (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂),
        shuffle_snd_fst X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂)]
      simp only [SmoothSite.product_left, SmoothSite.product_hom, pullback.map,
        pullback.lift_fst_assoc, reassoc_of% ht₁, inclusion_snd_fst X₁ X₂ Y₁ Y₂ I J,
        Category.assoc]
    · apply pullback.hom_ext (f := Y₂.hom) (g := Z₂.hom)
      · simp only [Category.assoc, hY₂, E, leftExteriorSupportMap, rightExteriorSupportMap,
          reassoc_of% (shuffle_snd_fst (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂),
          reassoc_of% (shuffle_snd_snd X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂))]
        simp only [SmoothSite.product_left, SmoothSite.product_hom, pullback.map,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc, reassoc_of% ht₂,
          inclusion_snd_snd X₁ X₂ Y₁ Y₂ I J,
          inclusion_snd_fst Y₁ Y₂ Z₁ Z₂ J K,
        Category.assoc]
      · simp only [Category.assoc, hZ₂, E, leftExteriorSupportMap, rightExteriorSupportMap,
          shuffle_snd_snd (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂,
          reassoc_of% (shuffle_snd_snd X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂))]
        simp only [SmoothSite.product_left, SmoothSite.product_hom, pullback.map,
          pullback.lift_snd_assoc, reassoc_of% ht₃, inclusion_snd_snd Y₁ Y₂ Z₁ Z₂ J K,
        Category.assoc]

section LeftCycle

variable (x : pullback (C := Scheme) X₁.hom X₂.hom)
  (y : pullback (C := Scheme) Y₁.hom Y₂.hom)
  (z : pullback (C := Scheme) Z₁.hom Z₂.hom)
  (hx : IsFiniteCorrespondencePoint X₁.hom X₂.hom x)
  (hy : IsFiniteCorrespondencePoint Y₁.hom Y₂.hom y)
  (hz : IsFiniteCorrespondencePoint Z₁.hom Z₂.hom z)

local notation "Ix" => integralComponentAt x
local notation "Iy" => integralComponentAt y
local notation "Iz" => integralComponentAt z
local notation "W" => correspondenceExteriorSupport X₁ X₂ Y₁ Y₂ Ix Iy
local notation "i" => correspondenceExteriorInclusion X₁ X₂ Y₁ Y₂ Ix Iy
set_option quotPrecheck false in
local notation "f" => pullback.fst (X X₁ Y₁).hom (X X₂ Y₂).hom ≫ (X X₁ Y₁).hom
set_option quotPrecheck false in
local notation "g" => pullback.fst Z₁.hom Z₂.hom ≫ Z₁.hom
set_option quotPrecheck false in
local notation "a₁" => pullback.fst
  (exteriorSupportSourceProjection X₁ X₂ Ix ≫ X₁.hom)
  (exteriorSupportSourceProjection Y₁ Y₂ Iy ≫ Y₁.hom) ≫
    exteriorSupportSourceProjection X₁ X₂ Ix ≫ X₁.hom
set_option quotPrecheck false in
local notation "b₁" => (Iz).subschemeι ≫ g

set_option maxHeartbeats 1600000 in
-- The component formula unfolds the finite pushforwards of the two original supports.
set_option linter.flexible false in
-- After expanding the two pullback maps, the composed projection equations are typed explicitly.
/-- The left iterated exterior prime is the original full triple support
cycle, including the local length on each intermediate component. -/
theorem leftExteriorPrime_eq_tripleCycle :
    letI : IsFinite (exteriorSupportSourceProjection X₁ X₂ Ix) := hx.1
    letI : IsFinite (exteriorSupportSourceProjection Y₁ Y₂ Iy) := hy.1
    letI : IsNoetherian (pullback (C := Scheme) a₁ b₁) :=
      Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
        (pullback.fst a₁ b₁ ≫ a₁)
    ((correspondenceExterior (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂)
      (correspondenceExteriorPrime X₁ X₂ Y₁ Y₂ x y hx hy)
      (singleFiniteCorrespondence Z₁.hom Z₂.hom z hz 1)).val =
      finiteCyclePushforward (leftExteriorSupportMap X₁ X₂ Y₁ Y₂ Z₁ Z₂ Ix Iy Iz)
        (AlgebraicCycle.fundamentalCycle (pullback a₁ b₁)) := by
  classical
  let : IsFinite (exteriorSupportSourceProjection X₁ X₂ Ix) := hx.1
  let : IsFinite (exteriorSupportSourceProjection Y₁ Y₂ Iy) := hy.1
  let : IsFinite (exteriorSupportSourceProjection Z₁ Z₂ Iz) := hz.1
  let : IsNoetherian W := correspondenceExteriorSupport_isNoetherian X₁ X₂ Y₁ Y₂ x y hx hy
  let : IsNoetherian (Iz).subscheme :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
      ((Iz).subschemeι ≫ pullback.fst Z₁.hom Z₂.hom ≫ Z₁.hom)
  let : IsNoetherian (pullback (C := Scheme) a₁ b₁) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k)) (pullback.fst a₁ b₁ ≫ a₁)
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite W).fintype
  let T := leftExteriorSupportMap X₁ X₂ Y₁ Y₂ Z₁ Z₂ Ix Iy Iz
  let A := (correspondenceExterior (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂).flip
    (singleFiniteCorrespondence Z₁.hom Z₂.hom z hz 1)
  change (A _).val = finiteCyclePushforward T _
  rw [correspondenceExteriorPrime_eq_sum_single X₁ X₂ Y₁ Y₂ x y hx hy, map_sum,
    fundamentalCycle_product_eq_sum_components a₁ b₁, map_sum]
  change (finiteCorrespondences (X (X X₁ Y₁) Z₁).hom (X (X X₂ Y₂) Z₂).hom).subtype
    (∑ t : genericPoints W, A _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  let v := correspondenceExteriorComponentPoint X₁ X₂ Y₁ Y₂ x y t
  let hv := correspondenceExteriorComponentPoint_admissible X₁ X₂ Y₁ Y₂ x y hx hy t
  let n := correspondenceExteriorComponentWeight X₁ X₂ Y₁ Y₂ x y t
  let j := (integralComponentAt t.val).subschemeι
  let q := (integralComponentAt v).subschemeι
  let u := integralComponentMap i t.val
  let : IsIso u := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion i t.val
  have hu : u ≫ q = j ≫ i := integralComponentMap_subschemeι i t.val
  have hi : i ≫ f = a₁ :=
    (Category.assoc _ _ _).trans (correspondenceExteriorInclusion_comp_base X₁ X₂ Y₁ Y₂ Ix Iy)
  have ht : (j ≫ a₁) ≫ 𝟙 (Spec (.of k)) = u ≫ (q ≫ f) :=
    (Category.comp_id _).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ f) hu).trans
        ((Category.assoc _ _ _).trans (congrArg (j ≫ ·) hi)))).symm
  let E := pullback.map (j ≫ a₁) b₁ (q ≫ f) b₁ u (𝟙 _) (𝟙 _) ht (by simp)
  let : IsIso E := inferInstanceAs (IsIso (pullback.map (j ≫ a₁) b₁
    (q ≫ f) b₁ u (𝟙 _) (𝟙 _) ht _))
  let : IsNoetherian (pullback (C := Scheme) (j ≫ a₁) b₁) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
      (pullback.fst (j ≫ a₁) b₁ ≫ j ≫ a₁)
  let : IsNoetherian (pullback (C := Scheme) (q ≫ f) b₁) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
      (pullback.fst (q ≫ f) b₁ ≫ q ≫ f)
  let S := (correspondenceExteriorShuffle (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂).hom
  let R := pullback.map (q ≫ f) b₁ f g q (Iz).subschemeι (𝟙 _) (by simp) (by simp)
  let : IsFinite R := by
    dsimp only [R]
    exact MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance rfl rfl
  let D := componentProductInclusion a₁ b₁ t.val
  have hD₁ : D ≫ pullback.fst a₁ b₁ = pullback.fst (j ≫ a₁) b₁ ≫ j :=
    pullback.lift_fst _ _ _
  have hD₂ : D ≫ pullback.snd a₁ b₁ = pullback.snd (j ≫ a₁) b₁ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hmap : E ≫ R ≫ S = D ≫ T := by
    apply (cancel_mono (inv S)).1
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    change E ≫ R = D ≫ _ ≫ S ≫ inv S
    rw [IsIso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · simp [E, R, pullback.map, Category.assoc, hu]
      exact ((reassoc_of% hD₁) i).symm
    · simp [E, R, pullback.map, Category.assoc]
      exact ((reassoc_of% hD₂) ((Iz).subschemeι)).symm
  have hr : exteriorPointCycle f g v z =
      finiteCyclePushforward R (AlgebraicCycle.fundamentalCycle _) := rfl
  change (A (singleFiniteCorrespondence _ _ v hv n)).val =
    finiteCyclePushforward T
      ((AlgebraicCycle.fundamentalCycle W t.val) •
        finiteCyclePushforward D (AlgebraicCycle.fundamentalCycle _))
  simp only [A, AddMonoidHom.flip_apply, correspondenceExterior_single, mul_one]
  have hn : AlgebraicCycle.fundamentalCycle W t.val = n :=
    AlgebraicCycle.fundamentalCycle_apply_generic W t
  have hs := finiteCyclePushforward_shuffle_exteriorPointCycle
    (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂ v z hv hz
  change n • (correspondenceExteriorPrime (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂ v z hv hz).val = _
  rw [hn, map_zsmul, ← hs, hr,
    ← finiteCyclePushforward_fundamentalCycle_iso (asIso E),
    finiteCyclePushforward_comp_apply, finiteCyclePushforward_comp_apply,
    finiteCyclePushforward_comp_apply]
  exact congrArg (n • ·) (finiteCyclePushforward_congr _ _ (by simpa [Category.assoc] using hmap) _)

end LeftCycle

section RightCycle

variable (x : pullback (C := Scheme) X₁.hom X₂.hom)
  (y : pullback (C := Scheme) Y₁.hom Y₂.hom)
  (z : pullback (C := Scheme) Z₁.hom Z₂.hom)
  (hx : IsFiniteCorrespondencePoint X₁.hom X₂.hom x)
  (hy : IsFiniteCorrespondencePoint Y₁.hom Y₂.hom y)
  (hz : IsFiniteCorrespondencePoint Z₁.hom Z₂.hom z)

local notation "Ix" => integralComponentAt x
local notation "Iy" => integralComponentAt y
local notation "Iz" => integralComponentAt z
local notation "W" => correspondenceExteriorSupport Y₁ Y₂ Z₁ Z₂ Iy Iz
local notation "i" => correspondenceExteriorInclusion Y₁ Y₂ Z₁ Z₂ Iy Iz
set_option quotPrecheck false in
local notation "f" => pullback.fst X₁.hom X₂.hom ≫ X₁.hom
set_option quotPrecheck false in
local notation "g" => pullback.fst (X Y₁ Z₁).hom (X Y₂ Z₂).hom ≫ (X Y₁ Z₁).hom
set_option quotPrecheck false in
local notation "a₁" => (Ix).subschemeι ≫ f
set_option quotPrecheck false in
local notation "b₁" => pullback.fst
  (exteriorSupportSourceProjection Y₁ Y₂ Iy ≫ Y₁.hom)
  (exteriorSupportSourceProjection Z₁ Z₂ Iz ≫ Z₁.hom) ≫
    exteriorSupportSourceProjection Y₁ Y₂ Iy ≫ Y₁.hom

set_option maxHeartbeats 1600000 in
-- The component formula unfolds the finite pushforwards of the two original supports.
set_option linter.flexible false in
-- After expanding the two pullback maps, the composed projection equations are typed explicitly.
/-- The right iterated exterior prime is the original full triple support
cycle, with the same intermediate coefficients. -/
theorem rightExteriorPrime_eq_tripleCycle :
    letI : IsFinite (exteriorSupportSourceProjection Y₁ Y₂ Iy) := hy.1
    letI : IsFinite (exteriorSupportSourceProjection Z₁ Z₂ Iz) := hz.1
    letI : IsNoetherian (pullback (C := Scheme) a₁ b₁) :=
      Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
        (pullback.fst a₁ b₁ ≫ a₁)
    ((correspondenceExterior X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂))
      (singleFiniteCorrespondence X₁.hom X₂.hom x hx 1)
      (correspondenceExteriorPrime Y₁ Y₂ Z₁ Z₂ y z hy hz)).val =
      finiteCyclePushforward (rightExteriorSupportMap X₁ X₂ Y₁ Y₂ Z₁ Z₂ Ix Iy Iz)
        (AlgebraicCycle.fundamentalCycle (pullback a₁ b₁)) := by
  classical
  let : IsFinite (exteriorSupportSourceProjection X₁ X₂ Ix) := hx.1
  let : IsFinite (exteriorSupportSourceProjection Y₁ Y₂ Iy) := hy.1
  let : IsFinite (exteriorSupportSourceProjection Z₁ Z₂ Iz) := hz.1
  let : IsNoetherian W := correspondenceExteriorSupport_isNoetherian Y₁ Y₂ Z₁ Z₂ y z hy hz
  let : IsNoetherian (Ix).subscheme :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
      ((Ix).subschemeι ≫ pullback.fst X₁.hom X₂.hom ≫ X₁.hom)
  let : IsNoetherian (pullback (C := Scheme) a₁ b₁) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k)) (pullback.fst a₁ b₁ ≫ a₁)
  let : IsNoetherian (pullback (C := Scheme) b₁ a₁) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k)) (pullback.fst b₁ a₁ ≫ b₁)
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite W).fintype
  let T := rightExteriorSupportMap X₁ X₂ Y₁ Y₂ Z₁ Z₂ Ix Iy Iz
  let e := pullbackSymmetry b₁ a₁
  let A := (correspondenceExterior X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂))
    (singleFiniteCorrespondence X₁.hom X₂.hom x hx 1)
  change (A _).val = finiteCyclePushforward T _
  rw [← finiteCyclePushforward_fundamentalCycle_iso e, finiteCyclePushforward_comp_apply,
    correspondenceExteriorPrime_eq_sum_single Y₁ Y₂ Z₁ Z₂ y z hy hz, map_sum,
    fundamentalCycle_product_eq_sum_components b₁ a₁, map_sum]
  change (finiteCorrespondences (X X₁ (X Y₁ Z₁)).hom (X X₂ (X Y₂ Z₂)).hom).subtype
    (∑ t : genericPoints W, A _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  let v := correspondenceExteriorComponentPoint Y₁ Y₂ Z₁ Z₂ y z t
  let hv := correspondenceExteriorComponentPoint_admissible Y₁ Y₂ Z₁ Z₂ y z hy hz t
  let n := correspondenceExteriorComponentWeight Y₁ Y₂ Z₁ Z₂ y z t
  let j := (integralComponentAt t.val).subschemeι
  let q := (integralComponentAt v).subschemeι
  let u := integralComponentMap i t.val
  let : IsIso u := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion i t.val
  have hu : u ≫ q = j ≫ i := integralComponentMap_subschemeι i t.val
  have hi : i ≫ g = b₁ :=
    (Category.assoc _ _ _).trans (correspondenceExteriorInclusion_comp_base Y₁ Y₂ Z₁ Z₂ Iy Iz)
  have ht : (j ≫ b₁) ≫ 𝟙 (Spec (.of k)) = u ≫ (q ≫ g) :=
    (Category.comp_id _).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g) hu).trans
        ((Category.assoc _ _ _).trans (congrArg (j ≫ ·) hi)))).symm
  let E₀ := pullback.map a₁ (j ≫ b₁) a₁ (q ≫ g) (𝟙 _) u (𝟙 _) (by simp) ht
  let E := (pullbackSymmetry (j ≫ b₁) a₁).hom ≫ E₀
  let : IsIso E₀ := inferInstanceAs (IsIso (pullback.map a₁ (j ≫ b₁)
    a₁ (q ≫ g) (𝟙 _) u (𝟙 _) _ ht))
  let : IsIso E := inferInstanceAs (IsIso ((pullbackSymmetry (j ≫ b₁) a₁).hom ≫ E₀))
  let : IsNoetherian (pullback (C := Scheme) (j ≫ b₁) a₁) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
      (pullback.fst (j ≫ b₁) a₁ ≫ j ≫ b₁)
  let : IsNoetherian (pullback (C := Scheme) a₁ (q ≫ g)) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
      (pullback.fst a₁ (q ≫ g) ≫ a₁)
  let p := (correspondenceExteriorShuffle X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂)).hom
  let R := pullback.map a₁ (q ≫ g) f g (Ix).subschemeι q (𝟙 _) (by simp) (by simp)
  let : IsFinite R := by
    dsimp only [R]
    exact MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance rfl rfl
  let D := componentProductInclusion b₁ a₁ t.val
  have hD₁ : D ≫ pullback.fst b₁ a₁ = pullback.fst (j ≫ b₁) a₁ ≫ j :=
    pullback.lift_fst _ _ _
  have hD₂ : D ≫ pullback.snd b₁ a₁ = pullback.snd (j ≫ b₁) a₁ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hmap : E ≫ R ≫ p = D ≫ e.hom ≫ T := by
    apply (cancel_mono (inv p)).1
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    change E ≫ R = D ≫ e.hom ≫ _ ≫ p ≫ inv p
    rw [IsIso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · simp [E, E₀, e, R, pullback.map, Category.assoc]
      have he : e.hom ≫ pullback.fst a₁ b₁ = pullback.snd b₁ a₁ :=
        pullbackSymmetry_hom_comp_fst b₁ a₁
      have hd := ((congrArg (D ≫ ·) ((reassoc_of% he) ((Ix).subschemeι))).trans
        ((reassoc_of% hD₂) ((Ix).subschemeι))).symm
      exact hd
    · simp [E, E₀, e, R, pullback.map, Category.assoc, hu]
      have he : e.hom ≫ pullback.snd a₁ b₁ = pullback.fst b₁ a₁ :=
        pullbackSymmetry_hom_comp_snd b₁ a₁
      have hd := ((congrArg (D ≫ ·) ((reassoc_of% he) i)).trans ((reassoc_of% hD₁) i)).symm
      exact hd
  have hr : exteriorPointCycle f g x v =
      finiteCyclePushforward R (AlgebraicCycle.fundamentalCycle _) := rfl
  change (A (singleFiniteCorrespondence _ _ v hv n)).val =
    finiteCyclePushforward (e.hom ≫ T)
      ((AlgebraicCycle.fundamentalCycle W t.val) •
        finiteCyclePushforward D (AlgebraicCycle.fundamentalCycle _))
  simp only [A, correspondenceExterior_single, one_mul]
  have hn : AlgebraicCycle.fundamentalCycle W t.val = n :=
    AlgebraicCycle.fundamentalCycle_apply_generic W t
  have hs := finiteCyclePushforward_shuffle_exteriorPointCycle
    X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂) x v hx hv
  change n • (correspondenceExteriorPrime X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂) x v hx hv).val = _
  rw [hn, map_zsmul, ← hs, hr,
    ← finiteCyclePushforward_fundamentalCycle_iso (asIso E),
    finiteCyclePushforward_comp_apply, finiteCyclePushforward_comp_apply,
    finiteCyclePushforward_comp_apply]
  exact congrArg (n • ·) (finiteCyclePushforward_congr _ _ (by simpa [Category.assoc] using hmap) _)

end RightCycle

section Naturality

variable (x : pullback (C := Scheme) X₁.hom X₂.hom)
  (y : pullback (C := Scheme) Y₁.hom Y₂.hom)
  (z : pullback (C := Scheme) Z₁.hom Z₂.hom)
  (hx : IsFiniteCorrespondencePoint X₁.hom X₂.hom x)
  (hy : IsFiniteCorrespondencePoint Y₁.hom Y₂.hom y)
  (hz : IsFiniteCorrespondencePoint Z₁.hom Z₂.hom z)

private theorem exteriorAssociatorNatural_single :
    let u : Cor.mk X₁ ⟶ Cor.mk X₂ := singleFiniteCorrespondence X₁.hom X₂.hom x hx 1
    let v : Cor.mk Y₁ ⟶ Cor.mk Y₂ := singleFiniteCorrespondence Y₁.hom Y₂.hom y hy 1
    let w : Cor.mk Z₁ ⟶ Cor.mk Z₂ := singleFiniteCorrespondence Z₁.hom Z₂.hom z hz 1
    Cor.exteriorProduct (Cor.exteriorProduct u v) w ≫
        (Cor.tensorAssociator (Cor.mk X₂) (Cor.mk Y₂) (Cor.mk Z₂)).hom =
      (Cor.tensorAssociator (Cor.mk X₁) (Cor.mk Y₁) (Cor.mk Z₁)).hom ≫
        Cor.exteriorProduct u (Cor.exteriorProduct v w) := by
  let I := integralComponentAt x
  let J := integralComponentAt y
  let K := integralComponentAt z
  let a := exteriorSupportSourceProjection X₁ X₂ I ≫ X₁.hom
  let b := exteriorSupportSourceProjection Y₁ Y₂ J ≫ Y₁.hom
  let c := exteriorSupportSourceProjection Z₁ Z₂ K ≫ Z₁.hom
  let : IsFinite (exteriorSupportSourceProjection X₁ X₂ I) := hx.1
  let : IsFinite (exteriorSupportSourceProjection Y₁ Y₂ J) := hy.1
  let : IsFinite (exteriorSupportSourceProjection Z₁ Z₂ K) := hz.1
  let : IsNoetherian (pullback (C := Scheme) (pullback.fst a b ≫ a) c) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
      (pullback.fst (pullback.fst a b ≫ a) c ≫ pullback.fst a b ≫ a)
  let : IsNoetherian (pullback (C := Scheme) a (pullback.fst b c ≫ b)) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
      (pullback.fst a (pullback.fst b c ≫ b) ≫ a)
  let u : Cor.mk X₁ ⟶ Cor.mk X₂ := singleFiniteCorrespondence X₁.hom X₂.hom x hx 1
  let v : Cor.mk Y₁ ⟶ Cor.mk Y₂ := singleFiniteCorrespondence Y₁.hom Y₂.hom y hy 1
  let w : Cor.mk Z₁ ⟶ Cor.mk Z₂ := singleFiniteCorrespondence Z₁.hom Z₂.hom z hz 1
  let e := α_ X₁ Y₁ Z₁
  let d := α_ X₂ Y₂ Z₂
  let p := (SmoothSite.productMap e.hom d.hom).left
  let : IsIso p := Cor.productMap_left_isIso e.hom d.hom
  intro
  refine Cor.comp_graph_iso_eq_graph_iso_comp e d
    (Cor.exteriorProduct (Cor.exteriorProduct u v) w)
    (Cor.exteriorProduct u (Cor.exteriorProduct v w)) ?_
  change finiteCyclePushforward p ((correspondenceExterior (X X₁ Y₁) (X X₂ Y₂) Z₁ Z₂)
      ((correspondenceExterior X₁ X₂ Y₁ Y₂) u v) w).val =
    ((correspondenceExterior X₁ X₂ (X Y₁ Z₁) (X Y₂ Z₂)) u
      ((correspondenceExterior Y₁ Y₂ Z₁ Z₂) v w)).val
  simp only [u, v, w, correspondenceExterior_single, one_mul, one_smul]
  rw [leftExteriorPrime_eq_tripleCycle, rightExteriorPrime_eq_tripleCycle,
    finiteCyclePushforward_comp_apply]
  let f := leftExteriorSupportMap X₁ X₂ Y₁ Y₂ Z₁ Z₂ I J K
  let g := rightExteriorSupportMap X₁ X₂ Y₁ Y₂ Z₁ Z₂ I J K
  let t := tripleProductAssoc a b c
  calc
    _ = finiteCyclePushforward (t.hom ≫ g) (AlgebraicCycle.fundamentalCycle _) :=
      finiteCyclePushforward_congr (f ≫ p) (t.hom ≫ g)
        (leftExteriorSupportMap_comp_associators X₁ X₂ Y₁ Y₂ Z₁ Z₂ I J K) _
    _ = _ := by
      rw [← finiteCyclePushforward_comp_apply, finiteCyclePushforward_fundamentalCycle_iso t]
      rfl

end Naturality

end Stacks.Chow

namespace AlgebraicGeometry.Cor

open Stacks.Chow

variable {k : Type u} [Field k]

/-- The original signed exterior tensor commutes with the graph associator. -/
theorem exteriorAssociatorNaturality : ExteriorAssociatorNaturality k := by
  rintro ⟨X₁⟩ ⟨X₂⟩ ⟨Y₁⟩ ⟨Y₂⟩ ⟨Z₁⟩ ⟨Z₂⟩ u v w
  let A := tensorAssociator (Cor.mk X₁) (Cor.mk Y₁) (Cor.mk Z₁)
  let B := tensorAssociator (Cor.mk X₂) (Cor.mk Y₂) (Cor.mk Z₂)
  let P := tensorObj (tensorObj (Cor.mk X₁) (Cor.mk Y₁)) (Cor.mk Z₁)
  let Q := tensorObj (Cor.mk X₂) (tensorObj (Cor.mk Y₂) (Cor.mk Z₂))
  let post := Preadditive.rightComp P B.hom
  let pre := Preadditive.leftComp Q A.hom
  let L₁ := post.comp ((exteriorProduct.flip w).comp (exteriorProduct.flip v))
  let R₁ := pre.comp (exteriorProduct.flip (exteriorProduct v w))
  have h₁ : L₁ = R₁ := by
    apply finiteCorrespondences.addHom_ext_one X₁.hom X₂.hom
    intro x hx
    let a : Cor.mk X₁ ⟶ Cor.mk X₂ := singleFiniteCorrespondence X₁.hom X₂.hom x hx 1
    change exteriorProduct (exteriorProduct a v) w ≫ B.hom =
      A.hom ≫ exteriorProduct a (exteriorProduct v w)
    let L₂ := post.comp ((exteriorProduct.flip w).comp (exteriorProduct a))
    let R₂ := pre.comp ((exteriorProduct a).comp (exteriorProduct.flip w))
    have h₂ : L₂ = R₂ := by
      apply finiteCorrespondences.addHom_ext_one Y₁.hom Y₂.hom
      intro y hy
      let b : Cor.mk Y₁ ⟶ Cor.mk Y₂ := singleFiniteCorrespondence Y₁.hom Y₂.hom y hy 1
      change exteriorProduct (exteriorProduct a b) w ≫ B.hom =
        A.hom ≫ exteriorProduct a (exteriorProduct b w)
      let L₃ := post.comp (exteriorProduct (exteriorProduct a b))
      let R₃ := pre.comp ((exteriorProduct a).comp (exteriorProduct b))
      have h₃ : L₃ = R₃ := by
        apply finiteCorrespondences.addHom_ext_one Z₁.hom Z₂.hom
        intro z hz
        exact exteriorAssociatorNatural_single X₁ X₂ Y₁ Y₂ Z₁ Z₂ x y z hx hy hz
      exact DFunLike.congr_fun h₃ w
    exact DFunLike.congr_fun h₂ v
  exact DFunLike.congr_fun h₁ u

end AlgebraicGeometry.Cor

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedProductCoverRows
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedProductCoverReflection
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothProductComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.SignedExactness
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.CoverComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Excision
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # The signed triangles of the represented cover and its product pairs -/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Category
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

private theorem map_inv_comp_of_comp_hom {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) {X Y : C} (e : X ≅ Y) {Z : D}
    (g : G.obj Y ⟶ Z) (f : G.obj X ⟶ Z) (h : f = G.map e.hom ≫ g) :
    G.map e.inv ≫ 𝟙 (G.obj X) ≫ f = g :=
  (congrArg (G.map e.inv ≫ ·) (Category.id_comp f)).trans ((G.mapIso e).inv_comp_eq.2 h)

private theorem map_with_identity_components {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) {X Y : C} {U V : D} (u : U ⟶ G.obj X) (f : X ⟶ Y)
    (v : G.obj Y ⟶ V) : u ≫ 𝟙 _ ≫ G.map (f ≫ 𝟙 _) ≫ v = u ≫ G.map f ≫ v := by
  rw [Category.id_comp, Category.comp_id]

private theorem map_projection_of_commSq {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) {X Y Z W : C} {A B V : D}
    (x : A ⟶ G.obj X) (y : B ⟶ G.obj Z) (f : A ⟶ B)
    (u : X ⟶ Y) (v : Y ⟶ W) (a : X ⟶ Z) (b : Z ⟶ W)
    (g : G.obj W ⟶ V) (h : B ⟶ V) (hc : u ≫ v = a ≫ b)
    (hn : f ≫ y = x ≫ G.map a) (hp : y ≫ G.map b ≫ g = h) :
    x ≫ 𝟙 _ ≫ G.map u ≫ G.map v ≫ g = f ≫ h := by
  rw [Category.id_comp, ← G.map_comp_assoc, hc, G.map_comp_assoc, ← reassoc_of% hn, hp]

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] supportedProductCorSheafify supportedProductSmoothSheafify

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => EffectiveMotivesMinus k
local notation "s" => singleTransferSheafMinus k
local notation "sₚ" => singleDerivedMinus k 0
local notation "A" => derivedNisnevichSheafification k
local notation "r" => effectiveReflection k
local notation "q" => singularPresheafToEffective k
local notation "M" => effectiveSmoothMotive k
set_option quotPrecheck false in
local notation "θ" => Cor.graphFunctorCompTensorRightIso (k := k)
local notation "γ" => Cor.graphFunctor k
set_option quotPrecheck false in
local notation "Rₚ" => γ ⋙ representableLarge k
local notation "R₁" => smoothTransferRepresentable k
set_option quotPrecheck false in
local notation "R₀" => Rₚ ⋙ sₚ

attribute [local instance] supportedProductAbelian

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionCommShift₂Int

attribute [local instance] supportedProductMonoidal supportedProductCommShift₂Int
  supportedProductLocalizationMonoidal supportedProductLocalizationMonoidalCommShift

attribute [local instance] supportedProductDerivedTensorAdditive
  derivedSheafification_preservesBinaryBiproducts relativeDerivedProduct_preservesBinaryBiproducts
  singleTransferSheafMinus_preservesBinaryBiproducts

variable {U V : Sm(k)} (j : U ⟶ V) [IsOpenImmersion j.left]

set_option quotPrecheck false in
local notation "P" => (projectivePairDerived k).obj (Arrow.mk j)
set_option quotPrecheck false in
local notation "F" => tensorLeft P ⋙ A

omit [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] in
private theorem reflectedDerivedMotiveRepresentableIso (Y : Sm(k)) :
    (sheafificationEffectiveReflectionIso k).inv.app ((R₀).obj Y) ≫
      (r).map ((derivedMotiveRepresentableIso k).hom.app Y) ≫
      (smoothTransferRepresentableEffectiveIso k).hom.app Y =
    (localizedRepresentableIso (Cor.mk Y)).hom := by
  change (sheafificationEffectiveReflectionIso k).inv.app _ ≫
    (r).map (derivedSheafificationSingleIso k ((Rₚ).obj Y)).hom ≫
    (singleSheafReflectionIso k ((Rₚ).obj Y)).hom = _
  unfold singleSheafReflectionIso localizedRepresentableIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, ← (r).map_comp_assoc]
  -- Both presentations use the same comparison of sheafification with a single.
  change _ ≫ (r).map
    ((derivedSheafificationSingleIso k ((Rₚ).obj Y)).hom ≫
      (derivedSheafificationSingleIso k ((Rₚ).obj Y)).inv) ≫ _ = _
  simp only [Iso.hom_inv_id, (r).map_id, Category.id_comp]
  rfl

/-- The ordinary cover triangle is transported through the actual singular reflection. -/
abbrev representedCoverTriangle (sq : Square Sm(k)) :=
  signedRowTriangle (representedCoverRow k sq)

/-- The chosen signed cofiber triangle of the represented cover. -/
abbrev representedCoverTriangleObj (sq : Square Sm(k)) :=
  let T := representedCoverTriangle k sq
  Triangle.mk (representedCoverRow k sq).f T.mor₂ T.connecting

/-- Reflection identifies the represented signed triangle with the ordinary cover. -/
def ordinaryCoverProjection (sq : Square Sm(k))
    (h : (transferMayerVietorisSequence k sq).ShortExact) :
    (q).mapTriangle.obj (representedCoverTriangleObj k sq) ≅
      effectiveMayerVietorisTriangleOfPushout k sq h := by
  let e := sheafificationEffectiveReflectionIso k
  let : (A).IsTriangulated := nisnevichDerivedMinus_isTriangulated k
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  let : NatTrans.CommShift e.inv ℤ := NatTrans.CommShift.of_iso_inv e ℤ
  let D₀ := representedCoverTriangleObj k sq
  let d₀ := signedRowTriangleToTransferIso k (representedCoverTriangle k sq) A h
    (ordinaryCoverRowIso k sq)
  exact (Functor.mapTriangleIso e.symm).app D₀ ≪≫
    (Functor.mapTriangleCompIso A r).app D₀ ≪≫
    (r).mapTriangle.mapIso d₀ ≪≫ effectiveMayerVietorisTriangleOfPushoutIso k sq h

/-- The pair tensor and reflection identify the signed triangle with the relative cover. -/
def pairCoverProjection (sq : Square Sm(k)) (h' : (productCoverRow k j sq).ShortExact) :
    ((q) ⋙ tensorLeft (effectivePairMotive k j)).mapTriangle.obj
      (representedCoverTriangleObj k sq) ≅
      effectivePairOpenCoverTriangle k h' := by
  let D₀ := representedCoverTriangleObj k sq
  let : (A).IsTriangulated := nisnevichDerivedMinus_isTriangulated k
  let : (tensorLeft P).IsTriangulated := derivedSignedTensorLeft_isTriangulated P
  let b := pairCoverToEffectiveCompIso k j
  let : NatTrans.CommShift b.hom ℤ := pairCoverToEffectiveCompIso_commShift k j
  let d₁ := signedRowTriangleToTransferIso k (representedCoverTriangle k sq) F h'
    (pairCoverRowIso k j sq)
  exact (Functor.mapTriangleIso b).app D₀ ≪≫ (Functor.mapTriangleCompIso F r).app D₀ ≪≫
    (r).mapTriangle.mapIso d₁ ≪≫ effectivePairOpenCoverTriangleIso k h'

/-- Effective reflection of transfer singles preserves the binary sums of the cover. -/
local instance representedTransferReflection_preservesBinaryBiproducts :
    PreservesBinaryBiproducts (effectiveTransferSheaf k) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

set_option maxHeartbeats 900000 in
-- Read the ordinary overlap component before tensoring the triangle.
omit [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] in
private theorem ordinaryCoverProjection_hom₁ (sq : Square Sm(k))
    (h : (transferMayerVietorisSequence k sq).ShortExact) :
    (ordinaryCoverProjection k sq h).hom.hom₁ =
      (localizedRepresentableIso (Cor.mk sq.X₁)).hom := by
  let L := localizedRepresentableIso (Cor.mk sq.X₁)
  dsimp only [ordinaryCoverProjection]
  simp only [Iso.trans_hom, Iso.app_hom, comp_hom₁, Functor.mapTriangleIso_hom_app_hom₁,
    Functor.mapTriangleCompIso_hom_app_hom₁, Functor.mapIso_hom, Functor.mapTriangle_map_hom₁,
    signedRowTriangleToTransferIso_hom₁, effectiveMayerVietorisTriangleOfPushoutIso_hom₁]
  let e := (sheafificationEffectiveReflectionIso k).inv.app ((R₀).obj sq.X₁)
  let a := (derivedMotiveRepresentableIso k).hom.app sq.X₁
  let b := (smoothTransferRepresentableEffectiveIso k).hom.app sq.X₁
  change e ≫ 𝟙 _ ≫ (r).map (a ≫ 𝟙 _) ≫ b = L.hom
  exact (map_with_identity_components r e a b).trans
    (reflectedDerivedMotiveRepresentableIso k sq.X₁)

set_option maxHeartbeats 950000 in
-- Read the actual augmentation under the ordinary union component.
omit [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] in
private theorem ordinaryCoverProjection_hom₃ (sq : Square Sm(k))
    (h : (transferMayerVietorisSequence k sq).ShortExact) :
    (ordinaryCoverProjection k sq h).hom.hom₃ =
      (q).map (representedCoverTriangle k sq).augmentation ≫
        (localizedRepresentableIso (Cor.mk sq.X₄)).hom := by
  let T := representedCoverTriangle k sq
  let f := T.augmentation
  let L := localizedRepresentableIso (Cor.mk sq.X₄)
  dsimp only [ordinaryCoverProjection]
  simp only [Iso.trans_hom, Iso.app_hom, comp_hom₃, Functor.mapTriangleIso_hom_app_hom₃,
    Functor.mapTriangleCompIso_hom_app_hom₃, Functor.mapIso_hom, Functor.mapTriangle_map_hom₃,
    signedRowTriangleToTransferIso_hom₃, effectiveMayerVietorisTriangleOfPushoutIso_hom₃,
    Functor.map_comp, Category.assoc]
  let e := (sheafificationEffectiveReflectionIso k).inv
  let a := (derivedMotiveRepresentableIso k).hom.app sq.X₄
  let b := (smoothTransferRepresentableEffectiveIso k).hom.app sq.X₄
  let m := (r).map ((A).map f)
  let x := e.app T.obj₃
  change x ≫ 𝟙 _ ≫ m ≫ (r).map (a ≫ 𝟙 _) ≫ b = (q).map f ≫ L.hom
  have hn : (q).map f ≫ e.app ((R₀).obj sq.X₄) = x ≫ m := e.naturality f
  calc
    _ = x ≫ m ≫ (r).map (a ≫ 𝟙 _) ≫ b := congrArg (x ≫ ·) (Category.id_comp _)
    _ = x ≫ m ≫ (r).map a ≫ b :=
      congrArg (fun t => x ≫ m ≫ (r).map t ≫ b) (Category.comp_id a)
    _ = (q).map f ≫ e.app ((R₀).obj sq.X₄) ≫ (r).map a ≫ b :=
      ((reassoc_of% hn) _).symm
    _ = _ := congrArg ((q).map f ≫ ·) (reflectedDerivedMotiveRepresentableIso k sq.X₄)

set_option maxHeartbeats 950000 in
-- Use the proved overlap of the product row as the first component.
private theorem pairCoverProjection_hom₁ (sq : Square Sm(k))
    (h' : (productCoverRow k j sq).ShortExact) :
    (pairCoverProjection k j sq h').hom.hom₁ =
      (pairCoverToEffectiveCompIso k j).hom.app ((R₀).obj sq.X₁) ≫
        (r).map (derivedProductPairEndIso k j sq.X₁).hom := by
  let c := (pairCoverToEffectiveCompIso k j).hom.app ((R₀).obj sq.X₁)
  let p := (derivedProductPairEndIso k j sq.X₁).hom
  dsimp only [pairCoverProjection]
  simp only [Iso.trans_hom, Iso.app_hom, comp_hom₁, Functor.mapTriangleIso_hom_app_hom₁,
    Functor.mapTriangleCompIso_hom_app_hom₁, Functor.mapIso_hom, Functor.mapTriangle_map_hom₁,
    signedRowTriangleToTransferIso_hom₁, pairCoverRowIso_hom₁]
  change c ≫ 𝟙 _ ≫ (r).map p ≫ 𝟙 _ = c ≫ (r).map p
  exact (congrArg (c ≫ ·) (Category.id_comp _)).trans
    (congrArg (c ≫ ·) (Category.comp_id _))

set_option maxHeartbeats 950000 in
-- The union component is the image of the augmentation followed by the pair comparison.
private theorem pairCoverProjection_hom₃ (sq : Square Sm(k))
    (h' : (productCoverRow k j sq).ShortExact) :
    (pairCoverProjection k j sq h').hom.hom₃ =
      (pairCoverToEffectiveCompIso k j).hom.app (representedCoverTriangle k sq).obj₃ ≫
        (r).map ((F).map (representedCoverTriangle k sq).augmentation) ≫
          (r).map (derivedProductPairEndIso k j sq.X₄).hom := by
  let T := representedCoverTriangle k sq
  let x := (pairCoverToEffectiveCompIso k j).hom.app T.obj₃
  let m := (F).map T.augmentation
  let p := (derivedProductPairEndIso k j sq.X₄).hom
  dsimp only [pairCoverProjection]
  simp only [Iso.trans_hom, Iso.app_hom, comp_hom₃, Functor.mapTriangleIso_hom_app_hom₃,
    Functor.mapTriangleCompIso_hom_app_hom₃, Functor.mapIso_hom, Functor.mapTriangle_map_hom₃,
    signedRowTriangleToTransferIso_hom₃, pairCoverRowIso_hom₃]
  change x ≫ 𝟙 _ ≫ (r).map (m ≫ p) ≫ 𝟙 _ = x ≫ (r).map m ≫ (r).map p
  calc
    _ = x ≫ (r).map (m ≫ p) ≫ 𝟙 _ := congrArg (x ≫ ·) (Category.id_comp _)
    _ = x ≫ (r).map (m ≫ p) := congrArg (x ≫ ·) (Category.comp_id _)
    _ = _ := congrArg (x ≫ ·) ((r).map_comp _ _)

/-- Tensoring the ordinary signed cover triangle with the relative motive
of an open pair gives the signed cover triangle of the actual product pairs. -/
def effectivePairProductOpenCoverTriangleIso (sq : Square Sm(k))
    (h : (transferMayerVietorisSequence k sq).ShortExact)
    (h' : (productCoverRow k j sq).ShortExact) :
    (tensorLeft (effectivePairMotive k j)).mapTriangle.obj
        (effectiveMayerVietorisTriangleOfPushout k sq h) ≅
      effectivePairOpenCoverTriangle k h' := by
  let R := tensorLeft (effectivePairMotive k j)
  exact R.mapTriangle.mapIso (ordinaryCoverProjection k sq h).symm ≪≫
    (Functor.mapTriangleCompIso q R).symm.app (representedCoverTriangleObj k sq) ≪≫
    pairCoverProjection k j sq h'

/-- The singular localization preserves the binary sums of the cover. -/
local instance effectiveLocalization_preservesBinaryBiproducts :
    PreservesBinaryBiproducts q := preservesBinaryBiproducts_of_preservesBiproducts _

/-- Left tensor in effective motives is additive in its right variable. -/
local instance supportedProductTensorAdditive (X : E) : (tensorLeft X).Additive := by
  let : (tensorLeft X).IsTriangulated := effectiveSignedTensorLeft_isTriangulated θ X
  infer_instance

/-- Left tensor in effective motives preserves the binary sums of the cover. -/
local instance tensorLeft_preservesBinaryBiproducts (X : E) :
    PreservesBinaryBiproducts (tensorLeft X) := by
  let : (tensorLeft X).IsTriangulated := effectiveSignedTensorLeft_isTriangulated θ X
  exact preservesBinaryBiproducts_of_preservesBiproducts _

/-- The biproduct of the two represented charts in the original row. -/
abbrev representedCoverBiprod (sq : Square Sm(k)) :=
  (R₀).obj sq.X₂ ⊞ (R₀).obj sq.X₃

/-- Localization identifies the represented biproduct with the two ordinary chart motives. -/
abbrev ordinaryCoverProjectiveBiprodIso (sq : Square Sm(k)) :
    (q).obj (representedCoverBiprod k sq) ≅ ((M).obj sq.X₂ ⊞ (M).obj sq.X₃) :=
  (q).mapBiprod _ _ ≪≫ biprod.mapIso (localizedRepresentableIso (Cor.mk sq.X₂))
    (localizedRepresentableIso (Cor.mk sq.X₃))

set_option maxHeartbeats 1100000 in
-- The two biproduct projections determine this endpoint under exact reflection.
omit [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] in
/-- The middle ordinary comparison uses the two represented chart comparisons. -/
theorem ordinaryCoverProjection_hom₂ (sq : Square Sm(k))
    (h : (transferMayerVietorisSequence k sq).ShortExact) :
    (ordinaryCoverProjection k sq h).hom.hom₂ = (ordinaryCoverProjectiveBiprodIso k sq).hom := by
  let e := (sheafificationEffectiveReflectionIso k).inv
  let δ (Y : Sm(k)) : (A).obj ((R₀).obj Y) ⟶ (s).obj ((R₁).obj Y) :=
    (derivedMotiveRepresentableIso k).hom.app Y
  let b (Y : Sm(k)) : (r).obj ((s).obj ((R₁).obj Y)) ⟶ (M).obj Y :=
    (smoothTransferRepresentableEffectiveIso k).hom.app Y
  let X := ((R₁).obj sq.X₂ ⊞ (R₁).obj sq.X₃)
  let X₀ := representedCoverBiprod k sq
  let z : (A).obj X₀ ⟶ (s).obj X := (ordinaryCoverRowIso k sq).hom.τ₂
  dsimp only [ordinaryCoverProjection]
  simp only [Iso.trans_hom, Iso.app_hom, comp_hom₂, Functor.mapTriangleIso_hom_app_hom₂,
    Functor.mapTriangleCompIso_hom_app_hom₂, Functor.mapIso_hom, Functor.mapTriangle_map_hom₂,
    signedRowTriangleToTransferIso_hom₂, effectiveMayerVietorisTriangleOfPushoutIso_hom₂]
  apply biprod.hom_ext
  · simp only [biprod.mapIso_hom, Functor.mapBiprod_hom, Category.assoc,
      biprod.map_fst, biprod.lift_fst_assoc]
    let f := (biprod.fst : X₀ ⟶ (R₀).obj sq.X₂)
    let g := (biprod.fst : X ⟶ (R₁).obj sq.X₂)
    change e.app X₀ ≫ 𝟙 ((r).obj ((A).obj X₀)) ≫ (r).map z ≫
      (r).map ((s).map g) ≫ b sq.X₂ = (q).map f ≫ (localizedRepresentableIso (Cor.mk sq.X₂)).hom
    have hz : z ≫ (s).map g = (A).map f ≫ δ sq.X₂ :=
      ordinaryCoverRowIso_hom₂_fst k sq
    have he : (q).map f ≫ e.app ((R₀).obj sq.X₂) = e.app X₀ ≫ (r).map ((A).map f) :=
      e.naturality f
    exact map_projection_of_commSq r (e.app X₀) (e.app ((R₀).obj sq.X₂)) ((q).map f)
      z ((s).map g) ((A).map f) (δ sq.X₂) (b sq.X₂) _ hz he
      (reflectedDerivedMotiveRepresentableIso k sq.X₂)
  · simp only [biprod.mapIso_hom, Functor.mapBiprod_hom, Category.assoc,
      biprod.map_snd, biprod.lift_snd_assoc]
    let f := (biprod.snd : X₀ ⟶ (R₀).obj sq.X₃)
    let g := (biprod.snd : X ⟶ (R₁).obj sq.X₃)
    change e.app X₀ ≫ 𝟙 ((r).obj ((A).obj X₀)) ≫ (r).map z ≫
      (r).map ((s).map g) ≫ b sq.X₃ = (q).map f ≫ (localizedRepresentableIso (Cor.mk sq.X₃)).hom
    have hz : z ≫ (s).map g = (A).map f ≫ δ sq.X₃ :=
      ordinaryCoverRowIso_hom₂_snd k sq
    have he : (q).map f ≫ e.app ((R₀).obj sq.X₃) = e.app X₀ ≫ (r).map ((A).map f) :=
      e.naturality f
    exact map_projection_of_commSq r (e.app X₀) (e.app ((R₀).obj sq.X₃)) ((q).map f)
      z ((s).map g) ((A).map f) (δ sq.X₃) (b sq.X₃) _ hz he
      (reflectedDerivedMotiveRepresentableIso k sq.X₃)

set_option maxHeartbeats 1100000 in
-- Compare the two actual component maps before composing with the inverse.
/-- The cover comparison on the overlap is the original relative product comparison. -/
theorem effectivePairProductOpenCoverTriangleIso_hom₁ (sq : Square Sm(k))
    (h : (transferMayerVietorisSequence k sq).ShortExact)
    (h' : (productCoverRow k j sq).ShortExact) :
    (effectivePairProductOpenCoverTriangleIso k j sq h h').hom.hom₁ =
      (effectivePairProductRightIso k j sq.X₁).hom := by
  let R := tensorLeft (effectivePairMotive k j)
  let O := ordinaryCoverProjection k sq h
  let V := pairCoverProjection k j sq h'
  let L := localizedRepresentableIso (Cor.mk sq.X₁)
  let g := (effectivePairProductRightIso k j sq.X₁).hom
  let c := (pairCoverToEffectiveCompIso k j).hom.app ((R₀).obj sq.X₁)
  let p := (derivedProductPairEndIso k j sq.X₁).hom
  refine map_inv_comp_of_comp_hom R (Triangle.π₁.mapIso O) g V.hom.hom₁ ?_
  have hO : (Triangle.π₁.mapIso O).hom = L.hom := ordinaryCoverProjection_hom₁ k sq h
  have hV : V.hom.hom₁ = c ≫ (r).map p := pairCoverProjection_hom₁ k j sq h'
  exact hV.trans ((reflectedDerivedProductPairEndIso k j sq.X₁).trans
    (congrArg (fun a => R.map a ≫ g) hO.symm))

set_option maxHeartbeats 1250000 in
-- The union component carries the actual represented augmentation through reflection.
/-- The cover comparison on the union is the original relative product comparison. -/
theorem effectivePairProductOpenCoverTriangleIso_hom₃ (sq : Square Sm(k))
    (h : (transferMayerVietorisSequence k sq).ShortExact)
    (h' : (productCoverRow k j sq).ShortExact) :
    (effectivePairProductOpenCoverTriangleIso k j sq h h').hom.hom₃ =
      (effectivePairProductRightIso k j sq.X₄).hom := by
  let T := representedCoverTriangle k sq
  let R := tensorLeft (effectivePairMotive k j)
  let O := ordinaryCoverProjection k sq h
  let V := pairCoverProjection k j sq h'
  let f := T.augmentation
  let L := localizedRepresentableIso (Cor.mk sq.X₄)
  let g := (effectivePairProductRightIso k j sq.X₄).hom
  let c := (pairCoverToEffectiveCompIso k j).hom
  let p := (derivedProductPairEndIso k j sq.X₄).hom
  refine map_inv_comp_of_comp_hom R (Triangle.π₃.mapIso O) g V.hom.hom₃ ?_
  have hO : (Triangle.π₃.mapIso O).hom = (q).map f ≫ L.hom :=
    ordinaryCoverProjection_hom₃ k sq h
  let m := (F).map f
  let x := c.app T.obj₃
  have hV : V.hom.hom₃ = x ≫ (r).map m ≫ (r).map p := pairCoverProjection_hom₃ k j sq h'
  have hn : R.map ((q).map f) ≫ c.app ((R₀).obj sq.X₄) = x ≫ (r).map m := c.naturality f
  calc
    _ = x ≫ (r).map m ≫ (r).map p := hV
    _ = R.map ((q).map f) ≫ c.app ((R₀).obj sq.X₄) ≫ (r).map p := ((reassoc_of% hn) _).symm
    _ = R.map ((q).map f) ≫ R.map L.hom ≫ g :=
      congrArg (R.map ((q).map f) ≫ ·) (reflectedDerivedProductPairEndIso k j sq.X₄)
    _ = R.map ((q).map f ≫ L.hom) ≫ g := (R.map_comp_assoc _ _ _).symm
    _ = _ := congrArg (fun a => R.map a ≫ g) hO.symm

set_option maxHeartbeats 850000 in
-- Project the four maps of the triangle comparison before identifying the coefficient biproduct.
/-- The relative middle component contains the identity of the functor-composition comparison. -/
theorem pairCoverProjection_hom₂ (sq : Square Sm(k))
    (h' : (productCoverRow k j sq).ShortExact) :
    (pairCoverProjection k j sq h').hom.hom₂ =
      (pairCoverToEffectiveCompIso k j).hom.app (representedCoverTriangleObj k sq).obj₂ ≫
        𝟙 ((r).obj ((F).obj (representedCoverTriangleObj k sq).obj₂)) ≫
          (r).map (pairCoverRowIso k j sq).hom.τ₂ ≫
            (effectivePairOpenCoverTriangleIso k h').hom.hom₂ := by
  dsimp only [pairCoverProjection]
  simp only [Iso.trans_hom, Iso.app_hom, comp_hom₂, Functor.mapTriangleIso_hom_app_hom₂,
    Functor.mapTriangleCompIso_hom_app_hom₂, Functor.mapIso_hom, Functor.mapTriangle_map_hom₂,
    signedRowTriangleToTransferIso_hom₂]

set_option maxHeartbeats 650000 in
-- The identity component of the functor-composition comparison is already fixed.
/-- The middle component is determined by its composite with the ordinary comparison. -/
theorem effectivePairProductOpenCoverTriangleIso_hom₂_of_comp (sq : Square Sm(k))
    (h : (transferMayerVietorisSequence k sq).ShortExact)
    (h' : (productCoverRow k j sq).ShortExact)
    (f : (tensorLeft (effectivePairMotive k j)).obj
        (effectiveMayerVietorisTriangleOfPushout k sq h).obj₂ ⟶
      (effectivePairOpenCoverTriangle k h').obj₂)
    (hf : (pairCoverProjection k j sq h').hom.hom₂ =
      (tensorLeft (effectivePairMotive k j)).map (ordinaryCoverProjection k sq h).hom.hom₂ ≫ f) :
    (effectivePairProductOpenCoverTriangleIso k j sq h h').hom.hom₂ = f :=
  map_inv_comp_of_comp_hom (tensorLeft (effectivePairMotive k j))
    (Triangle.π₂.mapIso (ordinaryCoverProjection k sq h)) f
    (pairCoverProjection k j sq h').hom.hom₂ hf

end AlgebraicGeometry.MotivicHomotopy

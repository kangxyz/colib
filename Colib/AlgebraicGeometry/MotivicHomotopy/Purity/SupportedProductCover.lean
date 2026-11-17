/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedProductCoverMiddle
import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ArrowMap
import Colib.CategoryTheory.Limits.BiproductComparison

/-! # The biproduct component of the product-pair cover comparison -/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Category
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] supportedProductCorSheafify supportedProductSmoothSheafify

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "NST" => LargeSheaves k
local notation "s" => singleTransferSheafMinus k
local notation "sₚ" => singleDerivedMinus k 0
local notation "A" => derivedNisnevichSheafification k
local notation "r" => effectiveReflection k
local notation "q" => singularPresheafToEffective k
local notation "M" => effectiveSmoothMotive k
local notation "γ" => Cor.graphFunctor k
set_option quotPrecheck false in
local notation "Rₚ" => γ ⋙ representableLarge k
set_option quotPrecheck false in
local notation "R₀" => Rₚ ⋙ sₚ

attribute [local instance] supportedProductAbelian

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionCommShift₂Int

attribute [local instance] supportedProductMonoidal supportedProductCommShift₂Int
  supportedProductLocalizationMonoidal supportedProductLocalizationMonoidalCommShift

attribute [local instance] representedTransferReflection_preservesBinaryBiproducts
  effectiveLocalization_preservesBinaryBiproducts supportedProductTensorAdditive
  tensorLeft_preservesBinaryBiproducts

variable {U V : Sm(k)} (j : U ⟶ V) [IsOpenImmersion j.left]

set_option quotPrecheck false in
local notation "P" => (projectivePairDerived k).obj (Arrow.mk j)
set_option quotPrecheck false in
local notation "F" => tensorLeft P ⋙ A

set_option quotPrecheck false in
local notation "Qₚ(" sq ")" => productCoverQuotientSquare k j sq

omit [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] in
private theorem effectivePairCoverIso_hom₂_mapBiprod {S T : Square Sm(k)} (i : S ⟶ T)
    (h : (transferPairOpenCoverSequence k i).ShortExact) :
    (effectivePairOpenCoverTriangleIso k h).hom.hom₂ =
      ((effectiveTransferSheaf k).mapBiprod (transferPairOpenCoverSquare k i).X₂
        (transferPairOpenCoverSquare k i).X₃).hom := (rfl)

set_option maxHeartbeats 650000 in
-- Paste the projection, functoriality and reflection squares at their typed endpoints.
private theorem reflectedPairCoverChartProjection (sq : Square Sm(k)) (Y : Sm(k))
    {W : DerivedCategory.Minus NST} (f : representedCoverBiprod k sq ⟶ (R₀).obj Y)
    (g : (s).obj (Qₚ(sq).X₂ ⊞ Qₚ(sq).X₃) ⟶ W) (d : (F).obj ((R₀).obj Y) ⟶ W)
    (p : (tensorLeft (effectivePairMotive k j)).obj ((M).obj Y) ⟶ (r).obj W)
    (hg : (pairCoverRowIso k j sq).hom.τ₂ ≫ g = (F).map f ≫ d)
    (hp : (pairCoverToEffectiveCompIso k j).hom.app ((R₀).obj Y) ≫ (r).map d =
      (tensorLeft (effectivePairMotive k j)).map (localizedRepresentableIso (Cor.mk Y)).hom ≫ p) :
    ((pairCoverToEffectiveCompIso k j).hom.app (representedCoverBiprod k sq) ≫
        (r).map (pairCoverRowIso k j sq).hom.τ₂) ≫ (r).map g =
      (tensorLeft (effectivePairMotive k j)).map
        ((q).map f ≫ (localizedRepresentableIso (Cor.mk Y)).hom) ≫
        p := by
  let H := tensorLeft (effectivePairMotive k j)
  let b := (pairCoverToEffectiveCompIso k j).hom
  let x := b.app (representedCoverBiprod k sq)
  let y := b.app ((R₀).obj Y)
  let z := (pairCoverRowIso k j sq).hom.τ₂
  let a := H.map ((q).map f)
  have hn : a ≫ y = x ≫ (r).map ((F).map f) := b.naturality f
  have hf : a ≫ (y ≫ (r).map d) = (x ≫ (r).map z) ≫ (r).map g :=
    CochainComplex.SplitFactorization.comp_map_of_commSq r ((F).map f) g z d a x y hg.symm hn
  exact hf.symm.trans ((congrArg (a ≫ ·) hp).trans (H.map_comp_assoc _ _ _).symm)

set_option maxHeartbeats 950000 in
-- Read the actual middle component before applying the chart projection equations.
private theorem pairCoverProjection_hom₂_comp_biprod (sq : Square Sm(k))
    (h' : (productCoverRow k j sq).ShortExact) :
    let B := effectiveTransferSheaf k
    let Q := Qₚ(sq)
    let b := (pairCoverToEffectiveCompIso k j).hom.app (representedCoverBiprod k sq)
    let m := (r).map (pairCoverRowIso k j sq).hom.τ₂
    (pairCoverProjection k j sq h').hom.hom₂ = (b ≫ m) ≫ (B.mapBiprod Q.X₂ Q.X₃).hom := by
  intro B Q b m
  let V := pairCoverProjection k j sq h'
  let c := (pairCoverToEffectiveCompIso k j).hom.app (representedCoverTriangleObj k sq).obj₂
  let d := (effectivePairOpenCoverTriangleIso k h').hom.hom₂
  have hc : c = b := rfl
  have hV : V.hom.hom₂ = c ≫ 𝟙 _ ≫ m ≫ d := pairCoverProjection_hom₂ k j sq h'
  have hd : d = (B.mapBiprod Q.X₂ Q.X₃).hom :=
    effectivePairCoverIso_hom₂_mapBiprod k (smoothPairProductCoverMap j sq) h'
  calc
    _ = c ≫ 𝟙 _ ≫ m ≫ d := hV
    _ = c ≫ m ≫ d := congrArg (c ≫ ·) (Category.id_comp (m ≫ d))
    _ = b ≫ m ≫ d := congrArg (· ≫ m ≫ d) hc
    _ = b ≫ m ≫ (B.mapBiprod Q.X₂ Q.X₃).hom := congrArg (fun t => b ≫ m ≫ t) hd
    _ = _ := (Category.assoc b m _).symm

-- The two cover presentations use the same product and product map on each chart.
attribute [local irreducible] SmoothSite.product SmoothSite.productMap
  localizedRepresentableIso effectivePairProductRightIso

set_option backward.isDefEq.respectTransparency true in
set_option linter.defProp false in
set_option maxHeartbeats 1200000 in
-- Apply the reflection calculation at the literal chart quotient.
private def reflectedPairCoverChartProjection_fst (sq : Square Sm(k)) :=
  let H := tensorLeft (effectivePairMotive k j)
  let Q := Qₚ(sq)
  let f : representedCoverBiprod k sq ⟶ (R₀).obj sq.X₂ := biprod.fst
  let g := (s).map (biprod.fst : Q.X₂ ⊞ Q.X₃ ⟶ Q.X₂)
  let d : (F).obj ((R₀).obj sq.X₂) ⟶ (s).obj Q.X₂ :=
    (derivedProductPairEndIso k j sq.X₂).hom
  let l := (localizedRepresentableIso (Cor.mk sq.X₂)).hom
  let p : H.obj ((M).obj sq.X₂) ⟶ (r).obj ((s).obj Q.X₂) :=
    (effectivePairProductRightIso k j sq.X₂).hom
  have hg : (pairCoverRowIso k j sq).hom.τ₂ ≫ g = (F).map f ≫ d :=
    pairCoverRowIso_hom₂_fst k j sq
  let y := (pairCoverToEffectiveCompIso k j).hom.app ((R₀).obj sq.X₂)
  have hp : y ≫ (r).map d = H.map l ≫ p := reflectedDerivedProductPairEndIso k j sq.X₂
  reflectedPairCoverChartProjection k j sq sq.X₂ f g d p hg hp

set_option backward.isDefEq.respectTransparency true in
set_option linter.defProp false in
set_option maxHeartbeats 1200000 in
-- Apply the reflection calculation at the literal chart quotient.
private def reflectedPairCoverChartProjection_snd (sq : Square Sm(k)) :=
  let H := tensorLeft (effectivePairMotive k j)
  let Q := Qₚ(sq)
  let f : representedCoverBiprod k sq ⟶ (R₀).obj sq.X₃ := biprod.snd
  let g := (s).map (biprod.snd : Q.X₂ ⊞ Q.X₃ ⟶ Q.X₃)
  let d : (F).obj ((R₀).obj sq.X₃) ⟶ (s).obj Q.X₃ :=
    (derivedProductPairEndIso k j sq.X₃).hom
  let l := (localizedRepresentableIso (Cor.mk sq.X₃)).hom
  let p : H.obj ((M).obj sq.X₃) ⟶ (r).obj ((s).obj Q.X₃) :=
    (effectivePairProductRightIso k j sq.X₃).hom
  have hg : (pairCoverRowIso k j sq).hom.τ₂ ≫ g = (F).map f ≫ d :=
    pairCoverRowIso_hom₂_snd k j sq
  let y := (pairCoverToEffectiveCompIso k j).hom.app ((R₀).obj sq.X₃)
  have hp : y ≫ (r).map d = H.map l ≫ p := reflectedDerivedProductPairEndIso k j sq.X₃
  reflectedPairCoverChartProjection k j sq sq.X₃ f g d p hg hp

set_option backward.isDefEq.respectTransparency true in
set_option linter.defProp false in
set_option maxHeartbeats 2700000 in
-- Paste the two reflected chart projections at their original biproducts.
private def reflectedPairCoverBiprodComparison (sq : Square Sm(k)) :=
  let H := tensorLeft (effectivePairMotive k j)
  let B := effectiveTransferSheaf k
  let Q := Qₚ(sq)
  let l₂ : (q).obj ((R₀).obj sq.X₂) ≅ (M).obj sq.X₂ := localizedRepresentableIso (Cor.mk sq.X₂)
  let l₃ : (q).obj ((R₀).obj sq.X₃) ≅ (M).obj sq.X₃ := localizedRepresentableIso (Cor.mk sq.X₃)
  let v₂ : H.obj ((M).obj sq.X₂) ≅ B.obj Q.X₂ := effectivePairProductRightIso k j sq.X₂
  let v₃ : H.obj ((M).obj sq.X₃) ≅ B.obj Q.X₃ := effectivePairProductRightIso k j sq.X₃
  let b := (pairCoverToEffectiveCompIso k j).hom.app (representedCoverBiprod k sq)
  let m := (r).map (pairCoverRowIso k j sq).hom.τ₂
  biprod.comp_mapBiprod_hom_eq_of_projections
    (C := DerivedCategory.Minus (LargePresheaves k)) (N := NST)
    (D := DerivedCategory.Minus NST) (E := EffectiveMotivesMinus k) q H s r
    (X₂ := (R₀).obj sq.X₂) (X₃ := (R₀).obj sq.X₃)
    (Q₂ := Q.X₂) (Q₃ := Q.X₃) (Y₂ := (M).obj sq.X₂) (Y₃ := (M).obj sq.X₃)
    l₂ l₃ v₂ v₃ (b ≫ m) (reflectedPairCoverChartProjection_fst k j sq)
    (reflectedPairCoverChartProjection_snd k j sq)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 2700000 in
-- Identify the two canonical isomorphisms before composing the middle maps.
/-- The relative cover comparison uses the original product comparison on both charts. -/
theorem effectivePairProductOpenCoverTriangleIso_hom₂ (sq : Square Sm(k))
    (h : (transferMayerVietorisSequence k sq).ShortExact)
    (h' : (productCoverRow k j sq).ShortExact) :
    (effectivePairProductOpenCoverTriangleIso k j sq h h').hom.hom₂ =
      (effectivePairProductOpenCoverMiddleIso k j sq h h').hom := by
  let H := tensorLeft (effectivePairMotive k j)
  let B := effectiveTransferSheaf k
  let Q := Qₚ(sq)
  let Y₂ := (M).obj sq.X₂
  let Y₃ := (M).obj sq.X₃
  let l₂ : (q).obj ((R₀).obj sq.X₂) ≅ Y₂ := localizedRepresentableIso (Cor.mk sq.X₂)
  let l₃ : (q).obj ((R₀).obj sq.X₃) ≅ Y₃ := localizedRepresentableIso (Cor.mk sq.X₃)
  let v₂ : H.obj Y₂ ≅ B.obj Q.X₂ := effectivePairProductRightIso k j sq.X₂
  let v₃ : H.obj Y₃ ≅ B.obj Q.X₃ := effectivePairProductRightIso k j sq.X₃
  let w₀ := ((q).mapBiprod ((R₀).obj sq.X₂) ((R₀).obj sq.X₃)) ≪≫ biprod.mapIso l₂ l₃
  let u₀ := H.mapBiprod Y₂ Y₃ ≪≫ biprod.mapIso v₂ v₃
  let w := ordinaryCoverProjectiveBiprodIso k sq
  let u := effectivePairProductOpenCoverMiddleIso k j sq h h'
  have hw : w₀ = w := rfl
  have hu : u₀ = u := rfl
  have hc := (pairCoverProjection_hom₂_comp_biprod k j sq h').trans
    (reflectedPairCoverBiprodComparison k j sq)
  have hcomp : H.map w₀.hom ≫ u₀.hom = H.map w.hom ≫ u.hom :=
    congrArg₂ (fun e e' => H.map e.hom ≫ e'.hom) hw hu
  have hd := hc.trans hcomp
  have ho := ordinaryCoverProjection_hom₂ k sq h
  have hm := hd.trans (congrArg (fun f => H.map f ≫ u.hom) ho.symm)
  exact effectivePairProductOpenCoverTriangleIso_hom₂_of_comp k j sq h h' u.hom hm

end AlgebraicGeometry.MotivicHomotopy

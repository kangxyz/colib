/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedProductCoverEndpoints
import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ArrowMap

/-! # Naturality of the derived comparison for product pairs -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]

attribute [local instance] productCoverComparisonCorSheafify
  productCoverComparisonSmoothSheafify productCoverComparisonAbelian

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "NST" => LargeSheaves k
local notation "s" => singleTransferSheafMinus k
local notation "sₚ" => singleDerivedMinus k 0
local notation "A" => derivedNisnevichSheafification k
set_option quotPrecheck false in
local notation "θ" => Cor.graphFunctorCompTensorRightIso (k := k)
set_option quotPrecheck false in
local notation "R₀" => (Cor.graphFunctor k ⋙ representableLarge k) ⋙ sₚ

attribute [local instance] derivedConvolutionMonoidalCategory
attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable

variable {U V : Sm(k)} (j : U ⟶ V) [IsOpenImmersion j.left]

set_option quotPrecheck false in
local notation "P" => (projectivePairDerived k).obj (Arrow.mk j)
set_option quotPrecheck false in
local notation "Src₀" => R₀ ⋙ tensorLeft P
set_option quotPrecheck false in
local notation "Src" => Src₀ ⋙ A
set_option quotPrecheck false in
local notation "Dst" => pairProductParameter k j ⋙ (transferPairCokernelFunctor k) ⋙ s
set_option quotPrecheck false in
local notation "augmentation(" Y ")" => projectiveSmoothParameterPairAugmentation (θ Y) (Arrow.mk j)
set_option quotPrecheck false in
local notation "quotientMap(" f ")" =>
  (s).map ((transferPairCokernelFunctor k).map (smoothParameterArrowMap f (Arrow.mk j)))

omit [IsOpenImmersion j.left] in
private theorem productCoverSource_map {Y Y' : Sm(k)} (f : Y ⟶ Y') :
    (Src).map f = (A).map ((Src₀).map f) :=
  Functor.comp_map Src₀ A f

omit [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [IsOpenImmersion j.left] in
private theorem productCoverTarget_map {Y Y' : Sm(k)} (f : Y ⟶ Y') :
    (Dst).map f = quotientMap(f) := by
  let J := pairProductParameter k j
  let Q := transferPairCokernelFunctor k
  have hf : J.map f = smoothParameterArrowMap f (Arrow.mk j) := (rfl)
  exact (Functor.comp_map J (Q ⋙ s) f).trans
    ((Functor.comp_map Q s (J.map f)).trans (congrArg (fun t => (s).map (Q.map t)) hf))

set_option maxHeartbeats 950000 in
-- Unfold the declared map at its hom endpoints.
omit [IsOpenImmersion j.left] in
private theorem productCoverComparison_hom (Y : Sm(k)) :
    derivedProductPairEndHom k j Y =
      (A).map (derivedProductPairConvolutionHom k j Y) ≫ augmentation(Y) := by
  simp only [derivedProductPairEndHom]
  rfl

set_option maxHeartbeats 1550000 in
-- Apply the exact sheafification before pasting the augmentation square.
omit [IsOpenImmersion j.left] in
private theorem composedDerivedProductPair_naturality {Y Y' : Sm(k)} (f : Y ⟶ Y') :
    (A).map ((Src₀).map f) ≫
        (A).map (derivedProductPairConvolutionHom k j Y') ≫ augmentation(Y') =
      ((A).map (derivedProductPairConvolutionHom k j Y) ≫ augmentation(Y)) ≫ quotientMap(f) := by
  let m := (Src₀).map f
  let m₀ := (tensorLeft P).map ((R₀).map f)
  let t := derivedProductPairCoefficientMap k j f
  let a := derivedProductPairConvolutionHom k j Y
  let a' := derivedProductPairConvolutionHom k j Y'
  let p := augmentation(Y)
  let p' := augmentation(Y')
  let g := quotientMap(f)
  have h₀ : m = m₀ := Functor.comp_map (R₀) (tensorLeft P) f
  have h₁ : m₀ ≫ a' = a ≫ t := derivedProductPairConvolutionHom_naturality k j f
  have h : m ≫ a' = a ≫ t := (congrArg (· ≫ a') h₀).trans h₁
  have hp : (A).map t ≫ p' = p ≫ g := derivedProductPairAugmentation_naturality k j f
  have hm : (A).map m ≫ (A).map a' = (A).map a ≫ (A).map t :=
    ((A).map_comp _ _).symm.trans (((A).congr_map h).trans ((A).map_comp _ _))
  exact CochainComplex.SplitFactorization.comp_map_of_commSq (𝟭 (DerivedCategory.Minus NST))
    ((A).map t) g p p' ((A).map m) ((A).map a) ((A).map a') hp hm

set_option maxHeartbeats 1550000 in
-- Transport the proved square along the literal maps of the source and target functors.
omit [IsOpenImmersion j.left] in
/-- The comparison carries an actual smooth parameter map to the map of quotient sheaves. -/
theorem derivedProductPairEndHom_naturality {Y Y' : Sm(k)} (f : Y ⟶ Y') :
    (Src).map f ≫ derivedProductPairEndHom k j Y' =
      derivedProductPairEndHom k j Y ≫ (Dst).map f := by
  let m := (A).map ((Src₀).map f)
  let a := (A).map (derivedProductPairConvolutionHom k j Y) ≫ augmentation(Y)
  let a' := (A).map (derivedProductPairConvolutionHom k j Y') ≫ augmentation(Y')
  let e := derivedProductPairEndHom k j Y
  let e' := derivedProductPairEndHom k j Y'
  have hl : (Src).map f ≫ e' = m ≫ a' :=
    (congrArg (· ≫ e') (productCoverSource_map k j f)).trans
      (congrArg (m ≫ ·) (productCoverComparison_hom k j Y'))
  have hr : e ≫ (Dst).map f = a ≫ quotientMap(f) :=
    (congrArg (· ≫ (Dst).map f) (productCoverComparison_hom k j Y)).trans
      (congrArg (a ≫ ·) (productCoverTarget_map k j f))
  exact hl.trans ((composedDerivedProductPair_naturality k j f).trans hr.symm)

set_option maxHeartbeats 1400000 in
-- Assemble the component isomorphisms with their proved naturality.
/-- The derived product-pair comparison carries every map of the smooth parameter. -/
def derivedProductPairEndNatIso : Src ≅ Dst :=
  NatIso.ofComponents (F := Src) (G := Dst) (derivedProductPairEndIso k j)
    (fun f => derivedProductPairEndHom_naturality k j f)

set_option maxHeartbeats 650000 in
-- Read the original component without expanding the naturality proof.
/-- The natural comparison has the stipulated projective quotient map on each parameter. -/
theorem derivedProductPairEndNatIso_hom_app (Y : Sm(k)) :
    (derivedProductPairEndNatIso k j).hom.app Y = (derivedProductPairEndIso k j Y).hom := by
  unfold derivedProductPairEndNatIso
  rfl

end AlgebraicGeometry.MotivicHomotopy

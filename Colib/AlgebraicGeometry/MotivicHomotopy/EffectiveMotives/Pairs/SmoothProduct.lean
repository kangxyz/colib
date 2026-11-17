/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothProductComparison
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothParameterNaturality
import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ArrowMap
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Naturality of relative effective motives for the smooth product -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

private theorem naturality_of_composed_comparisons {C : Type*} [Category* C]
    {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
    (d₀ : X ⟶ Y) (d₁ : X' ⟶ Y') (p₀ : Y ⟶ Z) (p₁ : Y' ⟶ Z')
    (m₀ : X ⟶ Z) (m₁ : X' ⟶ Z')
    (hd : f ≫ d₁ = d₀ ≫ g) (hp : g ≫ p₁ = p₀ ≫ h)
    (hm₀ : m₀ = d₀ ≫ p₀) (hm₁ : m₁ = d₁ ≫ p₁) : f ≫ m₁ = m₀ ≫ h := by
  rw [hm₀, hm₁]
  exact CochainComplex.SplitFactorization.comp_map_of_commSq
    (𝟭 C) g h p₀ p₁ f d₀ d₁ hp hd

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]

local instance smoothProductNaturalityCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance smoothProductNaturalitySmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))
local notation "E" => EffectiveMotivesMinus k
local notation "M" => effectiveSmoothMotive k
set_option quotPrecheck false in
local notation "θ" => Cor.graphFunctorCompTensorRightIso (k := k)

/-- The canonical abelian structure on the sheaves with transfers. -/
local instance smoothProductNaturalityAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The signed convolution tensor used to compare product pairs. -/
local instance smoothProductNaturalityMonoidal : MonoidalCategory E :=
  effectiveSignedConvolutionMonoidalCategory θ

attribute [local irreducible] transferRepresentable

set_option maxHeartbeats 2200000 in
-- The two squares retain the original effective pair motives as endpoints.
/-- The product comparison sends the first-variable map to the original map of pairs. -/
theorem effectivePairProductRightIso_naturality {U V U' V' : Sm}
    {j : U ⟶ V} {j' : U' ⟶ V'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (f : Arrow.mk j ⟶ Arrow.mk j') (Y : Sm) :
    ((effectivePairMotiveFunctor k).map f ▷ (M).obj Y) ≫
        (effectivePairProductRightIso k j' Y).hom =
      (effectivePairProductRightIso k j Y).hom ≫
        (effectivePairMotiveFunctor k).map ((parameterProduct Y).mapArrow.map f) := by
  let d := effectiveRepresentedRightParameterIso θ Y
  let p := effectiveSmoothParameterPairIso (θ Y) j
  let p' := effectiveSmoothParameterPairIso (θ Y) j'
  let g := (effectivePairMotiveFunctor k).map f
  let u := (tensorRight ((effectiveMotive k).obj (Cor.mk Y))).map g
  let v := (effectiveParameterTensor (θ Y)).map g
  let t := (effectivePairMotiveFunctor k).map ((parameterProduct Y).mapArrow.map f)
  let d₀ := d.hom.app (effectivePairMotive k j)
  let d₁ := d.hom.app (effectivePairMotive k j')
  have hd : u ≫ d₁ = d₀ ≫ v := d.hom.naturality g
  have hp : v ≫ p'.hom = p.hom ≫ t := effectiveSmoothParameterPairIso_naturality (θ Y) f
  exact naturality_of_composed_comparisons u v t d₀ d₁ p.hom p'.hom
    (effectivePairProductRightIso k j Y).hom (effectivePairProductRightIso k j' Y).hom
    hd hp (effectivePairProductRightIso_hom k j Y) (effectivePairProductRightIso_hom k j' Y)

set_option maxHeartbeats 2200000 in
-- The comparison retains the original projective and effective pair maps.
/-- In the second variable the comparison gives the original product by the parameter map. -/
theorem effectivePairProductRightIso_parameter {U V Y Y' : Sm}
    (j : U ⟶ V) [IsOpenImmersion j.left] (f : Y ⟶ Y') :
    (effectivePairMotive k j ◁ (M).map f) ≫ (effectivePairProductRightIso k j Y').hom =
      (effectivePairProductRightIso k j Y).hom ≫
        (effectivePairMotiveFunctor k).map (smoothParameterArrowMap f (Arrow.mk j)) := by
  let a := effectivePairMotive k j
  let d := effectiveRepresentedRightParameterIso θ Y
  let d' := effectiveRepresentedRightParameterIso θ Y'
  let e := effectiveSmoothParameterPairIso (θ Y) j
  let e' := effectiveSmoothParameterPairIso (θ Y') j
  let η := (curriedTensor (Cor k)).flip.map ((Cor.graphFunctor k).map f)
  have hη (X : Sm) : η.app (Cor.mk X) ≫ (θ Y').hom.app X =
      (θ Y).hom.app X ≫ (Cor.graphFunctor k).map ((parameterMap f).app X) := by
    change (Cor.rightExteriorParameterMap f).app (Cor.mk X) ≫ 𝟙 _ =
      𝟙 _ ≫ (Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X) f)
    rw [Category.comp_id, Category.id_comp]
    exact Cor.rightExteriorParameterMap_app f (Cor.mk X)
  let u := a ◁ (M).map f
  let v := (effectiveParameterTensorMap (θ Y) (θ Y') η).app a
  let t := (effectivePairMotiveFunctor k).map (smoothParameterArrowMap f (Arrow.mk j))
  let d₀ := d.hom.app a
  let d₁ := d'.hom.app a
  have hd : u ≫ d₁ = d₀ ≫ v := effectiveRepresentedRightParameterIso_naturality θ f a
  have he : v ≫ e'.hom = e.hom ≫ t :=
    effectiveSmoothParameterPairIso_parameter (θ Y) (θ Y') f η hη j
  exact naturality_of_composed_comparisons u v t d₀ d₁ e.hom e'.hom
    (effectivePairProductRightIso k j Y).hom (effectivePairProductRightIso k j Y').hom
    hd he (effectivePairProductRightIso_hom k j Y) (effectivePairProductRightIso_hom k j Y')

end AlgebraicGeometry.MotivicHomotopy

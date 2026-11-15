/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothParameter
import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ArrowMap

/-! # Naturality of the effective pair comparison for a fixed smooth parameter -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

private theorem hom_naturality_of_two_squares {C : Type*} [Category* C]
    {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
    (u₀ : X ⟶ Y) (u₁ : X' ⟶ Y') (v₀ : Y ⟶ Z) (v₁ : Y' ⟶ Z')
    (p₀ : X ⟶ Z) (p₁ : X' ⟶ Z')
    (hu : f ≫ u₁ = u₀ ≫ g) (hv : g ≫ v₁ = v₀ ≫ h)
    (hp₀ : p₀ = u₀ ≫ v₀) (hp₁ : p₁ = u₁ ≫ v₁) : f ≫ p₁ = p₀ ≫ h := by
  rw [hp₁, hp₀, ← Category.assoc, hu, Category.assoc, hv, Category.assoc]

variable {k : Type u} [Field k] [PerfectField k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S

/-- The canonical abelian structure on sheaves with transfers. -/
local instance fixedParameterNaturalityAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

variable [HasDerivedCategory.{w} (LargePresheaves k)] [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

variable {T : SmoothSite (Spec (CommRingCat.of k))} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅ parameterProduct T ⋙ Cor.graphFunctor k)

set_option quotPrecheck false in
local notation "M" => effectiveReflection k
local notation "G" => parameterProduct T

private def projectiveSmoothParameterEffectiveAugmentation (j : Arrow Sm) :
    (effectiveParameterTensor e).obj
        ((singularPresheafToEffective k).obj ((projectivePairDerived k).obj j)) ⟶
      (effectivePairMotiveFunctor k).obj ((G).mapArrow.obj j) :=
  (effectiveParameterTensorCompIso e).hom.app ((projectivePairDerived k).obj j) ≫
    (sheafificationEffectiveReflectionIso k).inv.app
      ((derivedParameterPushforward F).obj ((projectivePairDerived k).obj j)) ≫
        (M).map (projectiveSmoothParameterPairAugmentation e j)

set_option maxHeartbeats 1200000 in
-- First paste the projective, sheafification, and quotient squares on the original representatives.
private theorem projectiveSmoothParameterEffectiveAugmentation_naturality {i j : Arrow Sm}
    (φ : i ⟶ j) :
    (effectiveParameterTensor e).map ((singularPresheafToEffective k).map
        ((projectivePairDerived k).map φ)) ≫ projectiveSmoothParameterEffectiveAugmentation e j =
      projectiveSmoothParameterEffectiveAugmentation e i ≫
        (effectivePairMotiveFunctor k).map ((G).mapArrow.map φ) := by
  let T₀ := effectiveParameterTensor e
  let H₀ := derivedParameterPushforward F
  let q := singularPresheafToEffective k
  let b := (effectiveParameterTensorCompIso e).hom
  let d := (sheafificationEffectiveReflectionIso k).inv
  let f := (projectivePairDerived k).map φ
  let Pᵢ := (projectivePairDerived k).obj i
  let Pⱼ := (projectivePairDerived k).obj j
  let bᵢ := b.app Pᵢ
  let bⱼ := b.app Pⱼ
  let dᵢ := d.app (H₀.obj Pᵢ)
  let dⱼ := d.app (H₀.obj Pⱼ)
  let pᵢ := projectiveSmoothParameterPairAugmentation e i
  let pⱼ := projectiveSmoothParameterPairAugmentation e j
  let f₁ := T₀.map (q.map f)
  let f₂ := q.map (H₀.map f)
  let f₃ := (derivedNisnevichSheafification k).map (H₀.map f)
  let g := (singleTransferSheafMinus k).map
    ((transferPairCokernelFunctor k).map ((G).mapArrow.map φ))
  have hb : f₁ ≫ bⱼ = bᵢ ≫ f₂ := b.naturality f
  have hd : f₂ ≫ dⱼ = dᵢ ≫ (M).map f₃ := d.naturality (H₀.map f)
  have hp : f₃ ≫ pⱼ = pᵢ ≫ g := projectiveSmoothParameterPairAugmentation_naturality e φ
  have h : f₂ ≫ (dⱼ ≫ (M).map pⱼ) = (dᵢ ≫ (M).map pᵢ) ≫ (M).map g :=
    CochainComplex.SplitFactorization.comp_map_of_commSq (M) f₃ g pᵢ pⱼ f₂ dᵢ dⱼ hp hd
  change f₁ ≫ (bⱼ ≫ dⱼ ≫ (M).map pⱼ) = (bᵢ ≫ dᵢ ≫ (M).map pᵢ) ≫ (M).map g
  exact CochainComplex.SplitFactorization.comp_map_of_commSq (𝟭 (EffectiveMotivesMinus k))
    f₂ ((M).map g) (dᵢ ≫ (M).map pᵢ) (dⱼ ≫ (M).map pⱼ) f₁ bᵢ bⱼ h hb

set_option maxHeartbeats 650000 in
-- Use the original projective-pair square to identify the inverse comparison.
omit [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] in
private theorem effectiveProjectivePairIso_inv_naturality {U X U' X' : Sm}
    {i : U ⟶ X} {j : U' ⟶ X'} [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (φ : Arrow.mk i ⟶ Arrow.mk j) :
    (effectivePairMotiveFunctor k).map φ ≫ (effectiveProjectivePairIso j).inv =
      (effectiveProjectivePairIso i).inv ≫
        (singularPresheafToEffective k).map ((projectivePairDerived k).map φ) := by
  apply (cancel_epi (effectiveProjectivePairIso i).hom).mp
  rw [← Category.assoc, ← effectiveProjectivePairIso_naturality φ, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

set_option maxHeartbeats 750000 in
-- Keep the projective augmentation at its given effective endpoints.
private theorem effectiveSmoothParameterPairIso_hom_projective {U X : Sm}
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    (effectiveSmoothParameterPairIso e j).hom =
      (effectiveParameterTensor e).map (effectiveProjectivePairIso j).inv ≫
        projectiveSmoothParameterEffectiveAugmentation e (Arrow.mk j) := by
  unfold projectiveSmoothParameterEffectiveAugmentation
  exact effectiveSmoothParameterPairIso_hom e j

section FixedParameterNaturality

attribute [local irreducible] Cor.graphFunctor transferRepresentable

set_option maxHeartbeats 2200000 in
-- Compose the comparison of open pairs with the original projective augmentation square.
/-- The fixed effective parameter comparison gives the map of the original product pairs. -/
theorem effectiveSmoothParameterPairIso_naturality
    (e : Cor.graphFunctor k ⋙ F ≅ parameterProduct T ⋙ Cor.graphFunctor k)
    {U X U' X' : Sm}
    {i : U ⟶ X} {j : U' ⟶ X'} [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (φ : Arrow.mk i ⟶ Arrow.mk j) :
    (effectiveParameterTensor e).map ((effectivePairMotiveFunctor k).map φ) ≫
        (effectiveSmoothParameterPairIso e j).hom =
      (effectiveSmoothParameterPairIso e i).hom ≫
        (effectivePairMotiveFunctor k).map ((G).mapArrow.map φ) := by
  let T₀ := effectiveParameterTensor e
  let q := singularPresheafToEffective k
  let f := (projectivePairDerived k).map φ
  let g := (effectivePairMotiveFunctor k).map φ
  let u := T₀.map g
  let v := (effectivePairMotiveFunctor k).map ((G).mapArrow.map φ)
  let aᵢ := T₀.map (effectiveProjectivePairIso i).inv
  let aⱼ := T₀.map (effectiveProjectivePairIso j).inv
  let bᵢ := projectiveSmoothParameterEffectiveAugmentation e (Arrow.mk i)
  let bⱼ := projectiveSmoothParameterEffectiveAugmentation e (Arrow.mk j)
  let f₁ := T₀.map (q.map f)
  have ht : u ≫ aⱼ = aᵢ ≫ f₁ :=
    (T₀.map_comp _ _).symm.trans
      ((T₀.congr_map (effectiveProjectivePairIso_inv_naturality φ)).trans (T₀.map_comp _ _))
  have hb : f₁ ≫ bⱼ = bᵢ ≫ v := projectiveSmoothParameterEffectiveAugmentation_naturality e φ
  exact hom_naturality_of_two_squares u f₁ v aᵢ aⱼ bᵢ bⱼ
    (effectiveSmoothParameterPairIso e i).hom (effectiveSmoothParameterPairIso e j).hom
    ht hb (effectiveSmoothParameterPairIso_hom_projective e i)
    (effectiveSmoothParameterPairIso_hom_projective e j)

end FixedParameterNaturality

end AlgebraicGeometry.MotivicHomotopy

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Nested
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Stages
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.OpenGeometry
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.WindowData
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksFrontier.CategoryTheory.Abelian.SigmaExactness

/-!
# Exact windows of the coniveau tower

The signed triangles of nested complementary opens induce exact windows
in the support tower by exactness of filtered colimits of abelian groups.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme Opposite
open scoped CategoryTheory.Pretriangulated.Opposite

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

private theorem map_op_comp_eq {C D : Type*} [Category* C] [Category* D] (F : Cᵒᵖ ⥤ D)
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (i : Y ⟶ Z)
    (w : f ≫ g = h ≫ i) : F.map g.op ≫ F.map f.op = F.map i.op ≫ F.map h.op :=
  (F.map_comp g.op f.op).symm.trans
    ((F.congr_map (congrArg Quiver.Hom.op w)).trans (F.map_comp i.op h.op))

section RepresentedBoundary

variable {C : Type*} [Category* C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]

private abbrev representedBoundary (K : C) (n : ℤ) (T : Triangle C) :=
  (preadditiveYoneda.obj K).homologySequenceδ ((triangleOpEquivalence C).functor.obj (op T))
    n (n + 1) rfl

private theorem representedBoundary_naturality (K : C) (n : ℤ) (S T : Triangle C)
    (a : S.obj₁ ⟶ T.obj₁) (c : S.obj₃ ⟶ T.obj₃)
    (h : c ≫ T.mor₃ = S.mor₃ ≫ a⟦(1 : ℤ)⟧') :
    (preadditiveYoneda.obj (K⟦n⟧)).map a.op ≫ representedBoundary K n S =
      representedBoundary K n T ≫ (preadditiveYoneda.obj (K⟦n + 1⟧)).map c.op := by
  apply ConcreteCategory.hom_ext
  intro u
  let x : T.obj₁ ⟶ K⟦n⟧ := u
  let e := (shiftFunctorAdd' C n 1 (n + 1) rfl).inv.app K
  have hs : representedBoundary K n S (a ≫ x) = S.mor₃ ≫ (a ≫ x)⟦(1 : ℤ)⟧' ≫ e :=
    preadditiveYoneda_homologySequenceδ_apply S n (n + 1) rfl (a ≫ x)
  have ht : representedBoundary K n T x = T.mor₃ ≫ x⟦(1 : ℤ)⟧' ≫ e :=
    preadditiveYoneda_homologySequenceδ_apply T n (n + 1) rfl x
  have hcomp : S.mor₃ ≫ (a ≫ x)⟦(1 : ℤ)⟧' ≫ e = c ≫ T.mor₃ ≫ x⟦(1 : ℤ)⟧' ≫ e := by
    simp only [Functor.map_comp, Category.assoc, reassoc_of% h]
  change representedBoundary K n S (a ≫ x) = c ≫ representedBoundary K n T x
  exact hs.trans (hcomp.trans (congrArg (fun z : T.obj₃ ⟶ K⟦n + 1⟧ ↦ c ≫ z) ht.symm))

end RepresentedBoundary

section MiddleIso

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

private theorem distinguished_change_middle (T : Triangle C) (hT : T ∈ distTriang C)
    {B : C} (e : T.obj₂ ≅ B) (f : T.obj₁ ⟶ B) (g : B ⟶ T.obj₃)
    (hf : T.mor₁ ≫ e.hom = f) (hg : T.mor₂ = e.hom ≫ g) :
    Triangle.mk f g T.mor₃ ∈ distTriang C := by
  let S := Triangle.mk f g T.mor₃
  have h₁ : T.mor₁ ≫ e.hom = 𝟙 T.obj₁ ≫ f := hf.trans (Category.id_comp f).symm
  have h₂ : T.mor₂ ≫ 𝟙 T.obj₃ = e.hom ≫ g := (Category.comp_id T.mor₂).trans hg
  have h₃ : T.mor₃ ≫ (𝟙 T.obj₁)⟦(1 : ℤ)⟧' = 𝟙 T.obj₃ ≫ T.mor₃ := by
    rw [(shiftFunctor C (1 : ℤ)).map_id, Category.comp_id, Category.id_comp]
  exact isomorphic_distinguished T hT S (Triangle.isoMk T S (Iso.refl _) e (Iso.refl _)
    h₁ h₂ h₃).symm

end MiddleIso

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable (X : Sm(k))

private abbrev largerSupportArrow {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :=
  Arrow.mk (supportOpenInclusion k X ZW.1.2.1)

private abbrev smallerSupportArrow {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :=
  Arrow.mk (supportOpenInclusion k X ZW.1.1.1)

private abbrev relativeSupportArrow {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :=
  Arrow.mk (supportOpenMap k X ZW.2)

private def supportPairFirstArrow {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    relativeSupportArrow k X ZW ⟶ largerSupportArrow k X ZW :=
  Arrow.homMk' (𝟙 _) (supportOpenInclusion k X ZW.1.1.1) (by
    rw [Category.id_comp, supportOpenMap_comp_inclusion])

private def supportPairSecondArrow {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    largerSupportArrow k X ZW ⟶ smallerSupportArrow k X ZW :=
  Arrow.homMk' (supportOpenMap k X ZW.2) (𝟙 X) (by
    rw [Category.comp_id, supportOpenMap_comp_inclusion])

set_option maxHeartbeats 800000 in
-- The two arrow objects share an open complement defined through their indices.
private theorem supportPairFirstArrow_naturality {Y : Sm(k)} {a b : ℕ}
    {ZW : ConiveauSupportPairs k X a b} {ZW' : ConiveauSupportPairs k Y a b}
    (α : relativeSupportArrow k Y ZW' ⟶ relativeSupportArrow k X ZW)
    (β : largerSupportArrow k Y ZW' ⟶ largerSupportArrow k X ZW)
    (h₁ : α.left = β.left)
    (h₂ : α.right ≫ supportOpenInclusion k X ZW.1.1.1 =
      supportOpenInclusion k Y ZW'.1.1.1 ≫ β.right) :
    supportPairFirstArrow k Y ZW' ≫ β = α ≫ supportPairFirstArrow k X ZW := by
  apply Arrow.hom_ext
  · change (𝟙 _) ≫ β.left = α.left ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, h₁]
  · exact h₂.symm

private def supportPairMiddleArrowIso {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    Arrow.mk (supportOpenMap k X ZW.2 ≫ supportOpenInclusion k X ZW.1.1.1) ≅
      largerSupportArrow k X ZW :=
  Arrow.isoMk' _ _ (Iso.refl _) (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact (supportOpenMap_comp_inclusion k X ZW.2).symm)

private theorem supportPairFirstArrow_factor {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    nestedPairFirstArrow k (supportOpenMap k X ZW.2) (supportOpenInclusion k X ZW.1.1.1) ≫
      (supportPairMiddleArrowIso k X ZW).hom = supportPairFirstArrow k X ZW := by
  apply Arrow.hom_ext
  · exact Category.comp_id _
  · exact Category.comp_id _

private theorem supportPairSecondArrow_factor {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    (supportPairMiddleArrowIso k X ZW).hom ≫ supportPairSecondArrow k X ZW =
      nestedPairSecondArrow k (supportOpenMap k X ZW.2) (supportOpenInclusion k X ZW.1.1.1) := by
  apply Arrow.hom_ext
  · exact Category.id_comp _
  · exact Category.id_comp _

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "DM(" field ")" => EffectiveMotivesMinus field

/-- The abelian structure on sheaves with transfers used for the support triangles. -/
local instance coniveauBasicAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

private def supportPairBoundary {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    (effectivePairMotiveFunctor k).obj (smallerSupportArrow k X ZW) ⟶
      ((effectivePairMotiveFunctor k).obj (relativeSupportArrow k X ZW))⟦(1 : ℤ)⟧ :=
  effectiveNestedPairBoundary k (supportOpenMap k X ZW.2)
    (supportOpenInclusion k X ZW.1.1.1)

private def supportPairTriangle {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    Triangle DM(k) :=
  Triangle.mk ((effectivePairMotiveFunctor k).map (supportPairFirstArrow k X ZW))
    ((effectivePairMotiveFunctor k).map (supportPairSecondArrow k X ZW))
    (supportPairBoundary k X ZW)

set_option maxHeartbeats 900000 in
-- Identify the normalized pair maps from their individually typed geometric factorizations.
private theorem supportPairTriangle_distinguished {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    supportPairTriangle k X ZW ∈ distTriang DM(k) := by
  let F := effectivePairMotiveFunctor k
  let i := supportOpenMap k X ZW.2
  let j := supportOpenInclusion k X ZW.1.1.1
  let T : Triangle DM(k) := effectiveNestedPairTriangle k i j
  let e₀ := supportPairMiddleArrowIso k X ZW
  let e : T.obj₂ ≅ F.obj (largerSupportArrow k X ZW) := F.mapIso e₀
  let a₁ := nestedPairFirstArrow k i j
  let a₂ := nestedPairSecondArrow k i j
  let f := supportPairFirstArrow k X ZW
  let g := supportPairSecondArrow k X ZW
  have h₁ : T.mor₁ = F.map a₁ := effectiveNestedPairTriangle_mor₁ k i j
  have h₂ : T.mor₂ = F.map a₂ := effectiveNestedPairTriangle_mor₂ k i j
  have hf : T.mor₁ ≫ e.hom = F.map f :=
    (congrArg (· ≫ e.hom) h₁).trans ((F.map_comp a₁ e₀.hom).symm.trans
      (F.congr_map (supportPairFirstArrow_factor k X ZW)))
  have hg : T.mor₂ = e.hom ≫ F.map g :=
    h₂.trans ((F.congr_map (supportPairSecondArrow_factor k X ZW).symm).trans
      (F.map_comp e₀.hom g))
  have hT : T ∈ distTriang DM(k) := effectiveNestedPairTriangle_distinguished k i j
  exact distinguished_change_middle T hT e (F.map f) (F.map g) hf hg

private def supportPairOppositeTriangle {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    Triangle (DM(k)ᵒᵖ) :=
  (triangleOpEquivalence DM(k)).functor.obj (op (supportPairTriangle k X ZW))

set_option maxHeartbeats 800000 in
-- The comparison passes through the opposite of the effective category.
private theorem supportPairOppositeTriangle_distinguished {a b : ℕ}
    (ZW : ConiveauSupportPairs k X a b) : supportPairOppositeTriangle k X ZW ∈ distTriang _ :=
  op_distinguished _ (supportPairTriangle_distinguished k X ZW)

private def supportPairCohomologySequence {a b : ℕ} (K : DM(k)) (n : ℤ)
    (ZW : ConiveauSupportPairs k X a b) : ComposableArrows AddCommGrpCat.{w'} 5 :=
  (preadditiveYoneda.obj K).homologySequenceComposableArrows₅
    (supportPairOppositeTriangle k X ZW) n (n + 1) rfl

set_option maxHeartbeats 800000 in
-- The Hom sequence uses shifts in the full subcategory of effective motives.
private theorem supportPairCohomologySequence_exact {a b : ℕ} (K : DM(k)) (n : ℤ)
    (ZW : ConiveauSupportPairs k X a b) : (supportPairCohomologySequence k X K n ZW).Exact :=
  (preadditiveYoneda.obj K).homologySequenceComposableArrows₅_exact _
    (supportPairOppositeTriangle_distinguished k X ZW) n (n + 1) rfl

private def supportPairCohomologyBoundary {a b : ℕ} (K : DM(k)) (n : ℤ)
    (ZW : ConiveauSupportPairs k X a b) :
    (coniveauRelativeSupportDiagram k X K n a b).obj ZW ⟶
      (coniveauCohomologyDiagram k X K (n + 1) b).obj ZW.1.1 :=
  representedBoundary K n (supportPairTriangle k X ZW)

set_option maxHeartbeats 900000 in
-- The shifted Hom naturality statement uses the three actual relative motives.
/-- The signed nested-pair boundary before taking the colimit. -/
@[no_expose]
def coniveauRelativeSupportBoundary (K : DM(k)) (n : ℤ) (a b : ℕ) :
    coniveauRelativeSupportDiagram k X K n a b ⟶
      coniveauSupportPairsSmall k X a b ⋙ coniveauCohomologyDiagram k X K (n + 1) b where
  app ZW := supportPairCohomologyBoundary k X K n ZW
  naturality ZW ZW' f := by
    let α := (coniveauSupportPairsInclusion k X a b).map f.op
    let m : ZW.1.1.1 ⟶ ZW'.1.1.1 := homOfLE f.le.1
    let γ := (supportOpenPairFunctor k X).map m.op
    let F := effectivePairMotiveFunctor k
    have h : F.map γ ≫ supportPairBoundary k X ZW =
        supportPairBoundary k X ZW' ≫ (F.map α)⟦(1 : ℤ)⟧' :=
      effectiveNestedPairBoundary_naturality k
        (supportOpenMap k X ZW'.2) (supportOpenInclusion k X ZW'.1.1.1)
        (supportOpenMap k X ZW.2) (supportOpenInclusion k X ZW.1.1.1)
        (supportOpenMap k X f.le.2) (supportOpenMap k X f.le.1) (𝟙 X)
        (by rw [supportOpenMap_comp, supportOpenMap_comp])
        (by rw [Category.comp_id, supportOpenMap_comp_inclusion])
    let S : Triangle DM(k) := supportPairTriangle k X ZW'
    let T : Triangle DM(k) := supportPairTriangle k X ZW
    let f₁ : S.obj₁ ⟶ T.obj₁ := F.map α
    let f₃ : S.obj₃ ⟶ T.obj₃ := F.map γ
    have h₃ : f₃ ≫ T.mor₃ = S.mor₃ ≫ f₁⟦(1 : ℤ)⟧' := h
    exact representedBoundary_naturality K n S T f₁ f₃ h₃

set_option maxHeartbeats 900000 in
-- The two support-indexed functors share the effective pair cohomology functor.
/-- Restriction from the cohomology of the larger support to that of the window. -/
@[no_expose]
def coniveauRelativeSupportRestriction (K : DM(k)) (n : ℤ) (a b : ℕ) :
    coniveauSupportPairsLarge k X a b ⋙ coniveauCohomologyDiagram k X K n a ⟶
      coniveauRelativeSupportDiagram k X K n a b where
  app ZW := (effectivePairCohomology k K n).map (supportPairFirstArrow k X ZW).op
  naturality ZW ZW' f := by
    let H := effectivePairCohomology k K n
    let α := (coniveauSupportPairsInclusion k X a b).map f.op
    let m : ZW.1.2.1 ⟶ ZW'.1.2.1 := homOfLE f.le.2
    let β := (supportOpenPairFunctor k X).map m.op
    let r := supportPairFirstArrow k X ZW
    let r' := supportPairFirstArrow k X ZW'
    have h : r' ≫ β = α ≫ r := by
      refine supportPairFirstArrow_naturality k X α β rfl ?_
      change supportOpenMap k X f.le.1 ≫ supportOpenInclusion k X ZW.1.1.1 =
        supportOpenInclusion k X ZW'.1.1.1 ≫ 𝟙 X
      rw [Category.comp_id, supportOpenMap_comp_inclusion]
    exact map_op_comp_eq H r' β α r h

/-- The map on the cohomology of a closed support and its inverse image. -/
def closedSupportCohomologyPreimageMap {Y : Sm(k)} (K : DM(k)) (n : ℤ)
    (f : Y ⟶ X) (Z : TopologicalSpace.Closeds X.left) :
    (closedSupportCohomology k X K n).obj Z ⟶
      (closedSupportCohomology k Y K n).obj (supportPreimage k f Z) :=
  (effectivePairCohomology k K n).map (supportOpenPairPreimageMap k f Z).op

/-- The map on relative cohomology for a nested support pair and its inverse image. -/
def relativeSupportCohomologyPreimageMap {Y : Sm(k)} (K : DM(k)) (n : ℤ)
    (f : Y ⟶ X) [IsOpenImmersion f.left] {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    (coniveauRelativeSupportDiagram k X K n a b).obj ZW ⟶
      (coniveauRelativeSupportDiagram k Y K n a b).obj
        ((coniveauSupportPairsPreimage k f a b).obj ZW) :=
  (effectivePairCohomology k K n).map (supportPairPreimageMap k f ZW).op

set_option maxHeartbeats 900000 in
-- The inverse-image indices introduce two presentations of the same pair morphism.
/-- Ambient restriction commutes with the original map from a closed support to a window. -/
@[reassoc]
theorem coniveauRelativeSupportRestriction_app_naturality {Y : Sm(k)} (K : DM(k)) (n : ℤ)
    (f : Y ⟶ X) [IsOpenImmersion f.left] {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    (coniveauRelativeSupportRestriction k X K n a b).app ZW ≫
        relativeSupportCohomologyPreimageMap k X K n f ZW =
      closedSupportCohomologyPreimageMap k X K n f ZW.1.2.1 ≫
        (coniveauRelativeSupportRestriction k Y K n a b).app
          ((coniveauSupportPairsPreimage k f a b).obj ZW) := by
  let H := effectivePairCohomology k K n
  let e := (coniveauSupportPairsPreimage k f a b).obj ZW
  let α := supportPairPreimageMap k f ZW
  let β := supportOpenPairPreimageMap k f ZW.1.2.1
  let r := supportPairFirstArrow k X ZW
  let r' := supportPairFirstArrow k Y e
  have h : r' ≫ β = α ≫ r :=
    supportPairFirstArrow_naturality k X α β rfl (supportOpenPreimageMap_comp_inclusion k f _)
  exact (map_op_comp_eq H r' β α r h).symm

set_option maxHeartbeats 900000 in
-- The ambient and nested-pair formulations of the shifted map must agree.
/-- Ambient restriction commutes with the signed boundary of the original nested pairs. -/
@[reassoc]
theorem coniveauRelativeSupportBoundary_app_naturality {Y : Sm(k)} (K : DM(k)) (n : ℤ)
    (f : Y ⟶ X) [IsOpenImmersion f.left] {a b : ℕ} (ZW : ConiveauSupportPairs k X a b) :
    (coniveauRelativeSupportBoundary k X K n a b).app ZW ≫
        closedSupportCohomologyPreimageMap k X K (n + 1) f ZW.1.1.1 =
      relativeSupportCohomologyPreimageMap k X K n f ZW ≫
        (coniveauRelativeSupportBoundary k Y K n a b).app
          ((coniveauSupportPairsPreimage k f a b).obj ZW) := by
  let e := (coniveauSupportPairsPreimage k f a b).obj ZW
  let α := supportPairPreimageMap k f ZW
  let γ := supportOpenPairPreimageMap k f ZW.1.1.1
  let F := effectivePairMotiveFunctor k
  have h : F.map γ ≫ supportPairBoundary k X ZW =
      supportPairBoundary k Y e ≫ (F.map α)⟦(1 : ℤ)⟧' :=
    effectiveNestedPairBoundary_naturality k
      (supportOpenMap k Y e.2) (supportOpenInclusion k Y e.1.1.1)
      (supportOpenMap k X ZW.2) (supportOpenInclusion k X ZW.1.1.1)
      (supportOpenPreimageMap k f ZW.1.2.1) (supportOpenPreimageMap k f ZW.1.1.1) f
      (supportOpenPreimageMap_naturality k f ZW.2)
      (supportOpenPreimageMap_comp_inclusion k f ZW.1.1.1).symm
  let S : Triangle DM(k) := supportPairTriangle k Y e
  let T : Triangle DM(k) := supportPairTriangle k X ZW
  let f₁ : S.obj₁ ⟶ T.obj₁ := F.map α
  let f₃ : S.obj₃ ⟶ T.obj₃ := F.map γ
  have h₃ : f₃ ≫ T.mor₃ = S.mor₃ ≫ f₁⟦(1 : ℤ)⟧' := h
  exact (representedBoundary_naturality K n S T f₁ f₃ h₃).symm

set_option maxHeartbeats 800000 in
-- The concrete Hom expression must agree with the shifted Yoneda connecting map.
/-- On a representative, the boundary precomposes the shifted class with the signed triangle map. -/
theorem coniveauRelativeSupportBoundary_app_apply {a b : ℕ} (K : DM(k)) (n : ℤ)
    (ZW : ConiveauSupportPairs k X a b)
    (x : effectivePairMotive k (supportOpenMap k X ZW.2) ⟶ K⟦n⟧) :
    (coniveauRelativeSupportBoundary k X K n a b).app ZW x =
      effectiveNestedPairBoundary k (supportOpenMap k X ZW.2)
        (supportOpenInclusion k X ZW.1.1.1) ≫ x⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' DM(k) n 1 (n + 1) rfl).inv.app K :=
  preadditiveYoneda_homologySequenceδ_apply (supportPairTriangle k X ZW) n (n + 1) rfl x

private def supportPairsCohomologyExtension (K : DM(k)) (n : ℤ) (a b : ℕ) :
    coniveauSupportPairsSmall k X a b ⋙ coniveauCohomologyDiagram k X K n b ⟶
      coniveauSupportPairsLarge k X a b ⋙ coniveauCohomologyDiagram k X K n a where
  app ZW := (closedSupportCohomology k X K n).map (homOfLE ZW.2)
  naturality _ _ _ := by
    let F := closedSupportCohomology k X K n
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp]
    exact F.congr_map (Subsingleton.elim _ _)

set_option maxHeartbeats 850000 in
-- The diagram maps are identified with three consecutive terms of shifted Yoneda.
/-- The middle three terms before taking the colimit over nested support pairs. -/
def coniveauRelativeSupportShortComplex (K : DM(k)) (n : ℤ) (a b : ℕ) :
    ShortComplex (ConiveauSupportPairs k X a b ⥤ AddCommGrpCat.{w'}) :=
  ShortComplex.mk (coniveauRelativeSupportRestriction k X K n a b)
    (coniveauRelativeSupportBoundary k X K n a b) (by
      apply NatTrans.ext
      funext ZW
      exact (supportPairCohomologySequence_exact k X K n ZW).zero 1)

set_option maxHeartbeats 850000 in
-- The diagram maps are identified with three consecutive terms of shifted Yoneda.
private def supportStageShortComplex (K : DM(k)) (n : ℤ) (a b : ℕ) :
    ShortComplex (ConiveauSupportPairs k X a b ⥤ AddCommGrpCat.{w'}) :=
  ShortComplex.mk (supportPairsCohomologyExtension k X K n a b)
    (coniveauRelativeSupportRestriction k X K n a b) (by
      apply NatTrans.ext
      funext ZW
      exact (supportPairCohomologySequence_exact k X K n ZW).zero 0)

set_option maxHeartbeats 850000 in
-- The diagram maps are identified with three consecutive terms of shifted Yoneda.
private def supportBoundaryShortComplex (K : DM(k)) (n : ℤ) (a b : ℕ) :
    ShortComplex (ConiveauSupportPairs k X a b ⥤ AddCommGrpCat.{w'}) :=
  ShortComplex.mk (coniveauRelativeSupportBoundary k X K n a b)
    (supportPairsCohomologyExtension k X K (n + 1) a b) (by
      apply NatTrans.ext
      funext ZW
      exact (supportPairCohomologySequence_exact k X K n ZW).zero 2)

variable [UnivLE.{u, w'}]

set_option maxHeartbeats 850000 in
-- Exactness uses the diagram category and exactness of its filtered colimit functor.
/-- The two maps on the relative support diagrams are exact at the relative term
of their filtered colimit. -/
theorem coniveauRelativeSupportColimit_exact (K : DM(k)) (n : ℤ) (a b : ℕ) :
    ((coniveauRelativeSupportShortComplex k X K n a b).map
      (colim (J := ConiveauSupportPairs k X a b) (C := AddCommGrpCat.{w'}))).Exact := by
  let S := coniveauRelativeSupportShortComplex k X K n a b
  have hS : S.Exact := Stacks.SigmaExactness.exact_of_app S fun ZW ↦
    (supportPairCohomologySequence_exact k X K n ZW).exact 1
  exact hS.map _

/-- The cohomology of the larger support maps to the window by restricting each nested pair. -/
@[no_expose]
def coniveauCohomologyToWindow (K : DM(k)) (n : ℤ) (a b : ℕ) :
    coniveauCohomology k X K n a ⟶ coniveauRelativeSupportCohomology k X K n a b :=
  (Functor.Final.colimitIso (coniveauSupportPairsLarge k X a b)
    (coniveauCohomologyDiagram k X K n a)).inv ≫
      colimMap (coniveauRelativeSupportRestriction k X K n a b)

/-- The window maps to the next degree of the smaller support stage by the signed boundary. -/
@[no_expose]
def coniveauWindowBoundary (K : DM(k)) (n : ℤ) {a b : ℕ} (hab : a ≤ b) :
    coniveauRelativeSupportCohomology k X K n a b ⟶ coniveauCohomology k X K (n + 1) b := by
  letI := coniveauSupportPairsSmall_final k X hab
  exact colimMap (coniveauRelativeSupportBoundary k X K n a b) ≫
    (Functor.Final.colimitIso (coniveauSupportPairsSmall k X a b)
      (coniveauCohomologyDiagram k X K (n + 1) b)).hom

set_option maxHeartbeats 850000 in
-- The generator calculation passes through a final change of indices.
/-- On a generator from the larger support, the stage-to-window map is the pair restriction. -/
@[reassoc]
theorem ι_coniveauCohomologyToWindow (K : DM(k)) (n : ℤ) {a b : ℕ}
    (ZW : ConiveauSupportPairs k X a b) :
    colimit.ι (coniveauCohomologyDiagram k X K n a) ZW.1.2 ≫
        coniveauCohomologyToWindow k X K n a b =
      (coniveauRelativeSupportRestriction k X K n a b).app ZW ≫
        colimit.ι (coniveauRelativeSupportDiagram k X K n a b) ZW := by
  let F := coniveauCohomologyDiagram k X K n a
  let L := coniveauSupportPairsLarge k X a b
  let e := Functor.Final.colimitIso L F
  change colimit.ι F (L.obj ZW) ≫ e.inv ≫ _ = _
  rw [← Functor.Final.ι_colimitIso_hom L F ZW, Category.assoc, Iso.hom_inv_id_assoc, ι_colimMap]

set_option maxHeartbeats 850000 in
-- The generator calculation uses a final change of indices in the next degree.
/-- On a nested pair, the colimit boundary is its signed connecting map into the smaller support. -/
@[reassoc]
theorem ι_coniveauWindowBoundary (K : DM(k)) (n : ℤ) {a b : ℕ} (hab : a ≤ b)
    (ZW : ConiveauSupportPairs k X a b) :
    colimit.ι (coniveauRelativeSupportDiagram k X K n a b) ZW ≫
        coniveauWindowBoundary k X K n hab =
      (coniveauRelativeSupportBoundary k X K n a b).app ZW ≫
        colimit.ι (coniveauCohomologyDiagram k X K (n + 1) b) ZW.1.1 := by
  let := coniveauSupportPairsSmall_final k X hab
  simp only [coniveauWindowBoundary, ι_colimMap_assoc, Functor.Final.ι_colimitIso_hom]
  rfl

set_option maxHeartbeats 850000 in
-- Two presentations of the colimits are compared on their nested-support generators.
private theorem coniveauCohomologyTransition_eq_colimMap (K : DM(k)) (n : ℤ) {a b : ℕ}
    (hab : a ≤ b) :
    coniveauCohomologyTransition k X K n hab =
      (by
        letI := coniveauSupportPairsSmall_final k X hab
        exact (Functor.Final.colimitIso (coniveauSupportPairsSmall k X a b)
          (coniveauCohomologyDiagram k X K n b)).inv ≫
            colimMap (supportPairsCohomologyExtension k X K n a b) ≫
          (Functor.Final.colimitIso (coniveauSupportPairsLarge k X a b)
            (coniveauCohomologyDiagram k X K n a)).hom) := by
  let := coniveauSupportPairsSmall_final k X hab
  let M := coniveauSupportPairsSmall k X a b
  let L := coniveauSupportPairsLarge k X a b
  let F := coniveauCohomologyDiagram k X K n b
  let G := coniveauCohomologyDiagram k X K n a
  let e₁ := Functor.Final.colimitIso M F
  let e₂ := Functor.Final.colimitIso L G
  let α := supportPairsCohomologyExtension k X K n a b
  apply (cancel_epi e₁.hom).mp
  apply colimit.hom_ext
  intro ZW
  change colimit.ι (M ⋙ F) ZW ≫ e₁.hom ≫ coniveauCohomologyTransition k X K n hab =
    colimit.ι (M ⋙ F) ZW ≫ e₁.hom ≫ e₁.inv ≫ colimMap α ≫ e₂.hom
  rw [Functor.Final.ι_colimitIso_hom_assoc M F ZW, ι_coniveauCohomologyTransition,
    Iso.hom_inv_id_assoc, ι_colimMap_assoc, Functor.Final.ι_colimitIso_hom]
  exact (colimit.w G
    (homOfLE ZW.2 : (coniveauSupportsInclusion k X hab).obj ZW.1.1 ⟶ ZW.1.2)).symm

set_option maxHeartbeats 900000 in
-- The short complexes use colimits identified along the final projections.
/-- The stage transition followed by restriction to the window is zero. -/
@[reassoc]
theorem coniveauCohomologyTransition_comp_toWindow (K : DM(k)) (n : ℤ) {a b : ℕ}
    (hab : a ≤ b) : coniveauCohomologyTransition k X K n hab ≫
      coniveauCohomologyToWindow k X K n a b = 0 := by
  let := coniveauSupportPairsSmall_final k X hab
  let S := supportStageShortComplex k X K n a b
  let C := colim (J := ConiveauSupportPairs k X a b) (C := AddCommGrpCat.{w'})
  let A := S.map C
  let e₁ : A.X₁ ≅ coniveauCohomology k X K n b :=
    Functor.Final.colimitIso (coniveauSupportPairsSmall k X a b)
      (coniveauCohomologyDiagram k X K n b)
  let e₂ : A.X₂ ≅ coniveauCohomology k X K n a :=
    Functor.Final.colimitIso (coniveauSupportPairsLarge k X a b)
      (coniveauCohomologyDiagram k X K n a)
  rw [coniveauCohomologyTransition_eq_colimMap k X K n hab]
  change (e₁.inv ≫ A.f ≫ e₂.hom) ≫ e₂.inv ≫ A.g = 0
  have hzero : A.f ≫ A.g = 0 := A.zero
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, hzero, comp_zero]

set_option maxHeartbeats 900000 in
-- The short complexes use colimits identified along the final projections.
/-- The stage-to-window map followed by the signed boundary is zero. -/
@[reassoc]
theorem coniveauCohomologyToWindow_comp_boundary (K : DM(k)) (n : ℤ) {a b : ℕ}
    (hab : a ≤ b) : coniveauCohomologyToWindow k X K n a b ≫
      coniveauWindowBoundary k X K n hab = 0 := by
  let := coniveauSupportPairsSmall_final k X hab
  let S := coniveauRelativeSupportShortComplex k X K n a b
  let C := colim (J := ConiveauSupportPairs k X a b) (C := AddCommGrpCat.{w'})
  let A := S.map C
  let e₁ : A.X₁ ≅ coniveauCohomology k X K n a :=
    Functor.Final.colimitIso (coniveauSupportPairsLarge k X a b)
      (coniveauCohomologyDiagram k X K n a)
  let e₃ : A.X₃ ≅ coniveauCohomology k X K (n + 1) b :=
    Functor.Final.colimitIso (coniveauSupportPairsSmall k X a b)
      (coniveauCohomologyDiagram k X K (n + 1) b)
  change (e₁.inv ≫ A.f) ≫ A.g ≫ e₃.hom = 0
  have hzero : A.f ≫ A.g = 0 := A.zero
  rw [Category.assoc, reassoc_of% hzero, zero_comp, comp_zero]

set_option maxHeartbeats 900000 in
-- The short complexes use colimits identified along the final projections.
/-- The signed boundary followed by the next stage transition is zero. -/
@[reassoc]
theorem coniveauWindowBoundary_comp_transition (K : DM(k)) (n : ℤ) {a b : ℕ}
    (hab : a ≤ b) : coniveauWindowBoundary k X K n hab ≫
      coniveauCohomologyTransition k X K (n + 1) hab = 0 := by
  let := coniveauSupportPairsSmall_final k X hab
  let S := supportBoundaryShortComplex k X K n a b
  let C := colim (J := ConiveauSupportPairs k X a b) (C := AddCommGrpCat.{w'})
  let A := S.map C
  let e₂ : A.X₂ ≅ coniveauCohomology k X K (n + 1) b :=
    Functor.Final.colimitIso (coniveauSupportPairsSmall k X a b)
      (coniveauCohomologyDiagram k X K (n + 1) b)
  let e₃ : A.X₃ ≅ coniveauCohomology k X K (n + 1) a :=
    Functor.Final.colimitIso (coniveauSupportPairsLarge k X a b)
      (coniveauCohomologyDiagram k X K (n + 1) a)
  rw [coniveauCohomologyTransition_eq_colimMap k X K (n + 1) hab]
  change (A.f ≫ e₂.hom) ≫ e₂.inv ≫ A.g ≫ e₃.hom = 0
  have hzero : A.f ≫ A.g = 0 := A.zero
  rw [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hzero, zero_comp]

set_option maxHeartbeats 1000000 in
-- The short complexes use colimits identified along the final projections.
/-- The transition and restriction to the window are exact at the larger support stage. -/
theorem coniveauCohomologyStage_exact (K : DM(k)) (n : ℤ) {a b : ℕ} (hab : a ≤ b) :
    (ShortComplex.mk (coniveauCohomologyTransition k X K n hab)
      (coniveauCohomologyToWindow k X K n a b)
      (coniveauCohomologyTransition_comp_toWindow k X K n hab)).Exact := by
  let := coniveauSupportPairsSmall_final k X hab
  let S := supportStageShortComplex k X K n a b
  let e₁ := Functor.Final.colimitIso (coniveauSupportPairsSmall k X a b)
    (coniveauCohomologyDiagram k X K n b)
  let e₂ := Functor.Final.colimitIso (coniveauSupportPairsLarge k X a b)
    (coniveauCohomologyDiagram k X K n a)
  have hS : S.Exact := Stacks.SigmaExactness.exact_of_app S fun ZW ↦
    (supportPairCohomologySequence_exact k X K n ZW).exact 0
  let C := colim (J := ConiveauSupportPairs k X a b) (C := AddCommGrpCat.{w'})
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₁ := S.map C) e₁ e₂ (Iso.refl _) ?_ ?_) (hS.map C)
  · change e₁.hom ≫ coniveauCohomologyTransition k X K n hab = colimMap S.f ≫ e₂.hom
    rw [coniveauCohomologyTransition_eq_colimMap k X K n hab, Iso.hom_inv_id_assoc]
    rfl
  · change e₂.hom ≫ e₂.inv ≫ colimMap S.g = colimMap S.g ≫ 𝟙 _
    rw [Iso.hom_inv_id_assoc, Category.comp_id]
    rfl

set_option maxHeartbeats 1000000 in
-- The short complexes use colimits identified along the final projections.
/-- Restriction and the signed boundary are exact at the coniveau window. -/
theorem coniveauCohomologyWindow_exact (K : DM(k)) (n : ℤ) {a b : ℕ} (hab : a ≤ b) :
    (ShortComplex.mk (coniveauCohomologyToWindow k X K n a b)
      (coniveauWindowBoundary k X K n hab)
      (coniveauCohomologyToWindow_comp_boundary k X K n hab)).Exact := by
  let := coniveauSupportPairsSmall_final k X hab
  let S := coniveauRelativeSupportShortComplex k X K n a b
  let e₁ := Functor.Final.colimitIso (coniveauSupportPairsLarge k X a b)
    (coniveauCohomologyDiagram k X K n a)
  let e₃ := Functor.Final.colimitIso (coniveauSupportPairsSmall k X a b)
    (coniveauCohomologyDiagram k X K (n + 1) b)
  let C := colim (J := ConiveauSupportPairs k X a b) (C := AddCommGrpCat.{w'})
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₁ := S.map C) e₁ (Iso.refl _) e₃ ?_ ?_)
    (coniveauRelativeSupportColimit_exact k X K n a b)
  · change e₁.hom ≫ e₁.inv ≫ colimMap S.f = colimMap S.f ≫ 𝟙 _
    rw [Iso.hom_inv_id_assoc, Category.comp_id]
    rfl
  · change 𝟙 _ ≫ colimMap S.g ≫ e₃.hom = colimMap S.g ≫ e₃.hom
    rw [Category.id_comp]

set_option maxHeartbeats 1000000 in
-- The short complexes use colimits identified along the final projections.
/-- The boundary and next transition are exact at the smaller support stage. -/
theorem coniveauWindowBoundary_exact (K : DM(k)) (n : ℤ) {a b : ℕ} (hab : a ≤ b) :
    (ShortComplex.mk (coniveauWindowBoundary k X K n hab)
      (coniveauCohomologyTransition k X K (n + 1) hab)
      (coniveauWindowBoundary_comp_transition k X K n hab)).Exact := by
  let := coniveauSupportPairsSmall_final k X hab
  let S := supportBoundaryShortComplex k X K n a b
  let e₂ := Functor.Final.colimitIso (coniveauSupportPairsSmall k X a b)
    (coniveauCohomologyDiagram k X K (n + 1) b)
  let e₃ := Functor.Final.colimitIso (coniveauSupportPairsLarge k X a b)
    (coniveauCohomologyDiagram k X K (n + 1) a)
  have hS : S.Exact := Stacks.SigmaExactness.exact_of_app S fun ZW ↦
    (supportPairCohomologySequence_exact k X K n ZW).exact 2
  let C := colim (J := ConiveauSupportPairs k X a b) (C := AddCommGrpCat.{w'})
  refine ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₁ := S.map C) (Iso.refl _) e₂ e₃ ?_ ?_) (hS.map C)
  · change 𝟙 _ ≫ colimMap S.f ≫ e₂.hom = colimMap S.f ≫ e₂.hom
    rw [Category.id_comp]
  · change e₂.hom ≫ coniveauCohomologyTransition k X K (n + 1) hab = colimMap S.g ≫ e₃.hom
    rw [coniveauCohomologyTransition_eq_colimMap k X K (n + 1) hab, Iso.hom_inv_id_assoc]
    rfl

end AlgebraicGeometry.MotivicHomotopy

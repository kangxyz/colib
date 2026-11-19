/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.WindowData
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.PointSupport
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata.OpenPairs
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata.Topology
import Mathlib.CategoryTheory.Whiskering

/-! # The inclusion of one point group in a coniveau window -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

attribute [local instance] specializationOrder

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable (X : Sm(k))

/-- The points of a fixed codimension in the actual smooth scheme. -/
abbrev ConiveauPoints (p : ℕ) := {x : X.left // coheight x = (p : ℕ∞)}

variable {p : ℕ}

/-- A representative on `U` at `x` has support in the relative complement of
`closure{x} \ U` inside `closure{x}`. -/
def pointSupportWindowIndex (x : ConiveauPoints k X p)
    (U : PointSupportNeighborhoods k X x.1) : ConiveauSupportPairs k X p (p + 1) := by
  let C : Closeds X.left := Closeds.closure {x.1}
  refine ⟨(⟨C ⊓ U.1.compl, ?_⟩, ⟨C, ?_⟩), inf_le_left⟩
  · rintro y ⟨hyC, hyU⟩
    exact Closeds.succ_le_coheight_of_mem_pointClosure hyC
      (fun hyx ↦ hyU (hyx.symm ▸ U.2)) x.2.ge
  · intro y hyC
    exact Closeds.le_coheight_of_mem_pointClosure hyC x.2.ge

/-- Shrinking the neighbourhood enlarges exactly the removed higher-codimension subset. -/
def pointSupportWindowIndices (x : ConiveauPoints k X p) :
    (PointSupportNeighborhoods k X x.1)ᵒᵖ ⥤ ConiveauSupportPairs k X p (p + 1) where
  obj U := pointSupportWindowIndex k X x U.unop
  map f := homOfLE ⟨inf_le_inf_left _ (Set.compl_subset_compl.mpr f.unop.le), le_rfl⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem pointSupportWindow_cover (x : ConiveauPoints k X p)
    (U : PointSupportNeighborhoods k X x.1) :
    (pointSupportWindowIndex k X x U).1.2.1.compl ⊔ U.1 =
      (pointSupportWindowIndex k X x U).1.1.1.compl := by
  classical
  ext y
  change (y ∉ closure {x.1} ∨ y ∈ U.1) ↔ ¬(y ∈ closure {x.1} ∧ y ∉ U.1)
  tauto

/-- The literal inclusion from the support on the neighbourhood to the pair in the window. -/
def pointSupportWindowArrowMap (x : ConiveauPoints k X p)
    (U : PointSupportNeighborhoods k X x.1) :
    pointSupportPair k X x.1 U ⟶
      (coniveauSupportPairsInclusion k X p (p + 1)).obj
        (op (pointSupportWindowIndex k X x U)) :=
  relativeOpenPairRestriction k X (Set.compl_subset_compl.mpr (pointSupportWindowIndex k X x U).2)
    (by rw [← pointSupportWindow_cover k X x U]; exact le_sup_right)

private theorem pointSupportWindowArrowMap_naturality (x : ConiveauPoints k X p)
    {U V : (PointSupportNeighborhoods k X x.1)ᵒᵖ} (i : U ⟶ V) :
    pointSupportWindowArrowMap k X x V.unop ≫
        (coniveauSupportPairsInclusion k X p (p + 1)).map
          ((pointSupportWindowIndices k X x).map i).op =
      (pointSupportPairFunctor k X x.1).map i.unop ≫
        pointSupportWindowArrowMap k X x U.unop := by
  let B := (Closeds.closure {x.1}).compl
  let S := SmoothSite.opensFunctor X
  let eU : U.unop.1 ≤ (pointSupportWindowIndex k X x U.unop).1.1.1.compl :=
    le_sup_right.trans (pointSupportWindow_cover k X x U.unop).le
  let eV : V.unop.1 ≤ (pointSupportWindowIndex k X x V.unop).1.1.1.compl :=
    le_sup_right.trans (pointSupportWindow_cover k X x V.unop).le
  let h : (pointSupportWindowIndex k X x V.unop).1.1.1.compl ≤
      (pointSupportWindowIndex k X x U.unop).1.1.1.compl :=
    Set.compl_subset_compl.mpr ((pointSupportWindowIndices k X x).map i).le.1
  apply Arrow.hom_ext
  · change S.map (homOfLE (inf_le_right : V.unop.1 ⊓ B ≤ B)) ≫
      S.map (homOfLE (le_rfl : B ≤ B)) =
        S.map (homOfLE (inf_le_inf_right B i.unop.le)) ≫
          S.map (homOfLE (inf_le_right : U.unop.1 ⊓ B ≤ B))
    rw [← S.map_comp, ← S.map_comp]
    exact congrArg S.map (Subsingleton.elim _ _)
  · change S.map (homOfLE eV) ≫ S.map (homOfLE h) =
      S.map (homOfLE i.unop.le) ≫ S.map (homOfLE eU)
    rw [← S.map_comp, ← S.map_comp]
    exact congrArg S.map (Subsingleton.elim _ _)

private theorem map_op_comp_eq {A B : Type*} [Category* A] [Category* B] (F : Aᵒᵖ ⥤ B)
    {J K L M : A} {a : J ⟶ K} {b : K ⟶ M} {c : J ⟶ L} {d : L ⟶ M}
    (e : a ≫ b = c ≫ d) : F.map b.op ≫ F.map a.op = F.map d.op ≫ F.map c.op :=
  (F.map_comp b.op a.op).symm.trans
    ((F.congr_map (congrArg Quiver.Hom.op e)).trans (F.map_comp d.op c.op))

private def coconeFromStages {J C : Type*} [Category* J] [Category* C] (G : J ⥤ C)
    (T : C) (a : ∀ j, G.obj j ⟶ T)
    (w : ∀ {i j : J} (f : i ⟶ j), G.map f ≫ a j = a i) : Cocone G where
  pt := T
  ι := { app := a, naturality := fun i _ f ↦ (w f).trans (Category.comp_id (a i)).symm }

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "DM(" field ")" => EffectiveMotivesMinus field

/-- The cohomology map on the original point-neighbourhood representative. -/
abbrev pointSupportWindowRestrictionMap (K : DM(k)) (n : ℤ)
    (x : ConiveauPoints k X p) (U : PointSupportNeighborhoods k X x.1) :
    (coniveauRelativeSupportDiagram k X K n p (p + 1)).obj (pointSupportWindowIndex k X x U) ⟶
      (pointSupportCohomologyDiagram k X K n x.1).obj (op U) :=
  (effectivePairCohomology k K n).map (pointSupportWindowArrowMap k X x U).op

/-- The point-neighbourhood map of the window stage is an open excision. -/
theorem pointSupportWindowRestrictionMap_isIso (K : DM(k)) (n : ℤ)
    (x : ConiveauPoints k X p) (U : PointSupportNeighborhoods k X x.1) :
    IsIso (pointSupportWindowRestrictionMap k X K n x U) := by
  let ZW := pointSupportWindowIndex k X x U
  let h : ZW.1.2.1.compl ≤ ZW.1.1.1.compl := Set.compl_subset_compl.mpr ZW.2
  let hV : U.1 ≤ ZW.1.1.1.compl := le_sup_right.trans (pointSupportWindow_cover k X x U).le
  let H := effectivePairCohomology k K n
  let d := relativeOpenPairRestriction k X h hV
  let A := (coniveauRelativeSupportDiagram k X K n p (p + 1)).obj ZW
  let B := (pointSupportCohomologyDiagram k X K n x.1).obj (op U)
  let f : A ⟶ B := pointSupportWindowRestrictionMap k X K n x U
  let f' : A ⟶ B := H.map d.op
  have heq : f = f' := rfl
  have hf : IsIso f' := isIso_relativeOpenPairCohomology_openExcision k X K n h hV
    (pointSupportWindow_cover k X x U)
  exact (show IsIso f from heq.symm ▸ hf)

/-- Restriction from the window stage to its representative at the indicated point. -/
def pointSupportWindowRestrictionIso (K : DM(k)) (n : ℤ) (x : ConiveauPoints k X p)
    (U : PointSupportNeighborhoods k X x.1) :
    (coniveauRelativeSupportDiagram k X K n p (p + 1)).obj (pointSupportWindowIndex k X x U) ≅
      (pointSupportCohomologyDiagram k X K n x.1).obj (op U) :=
  @asIso AddCommGrpCat.{w'} _ _ _ (pointSupportWindowRestrictionMap k X K n x U)
    (pointSupportWindowRestrictionMap_isIso k X K n x U)

private def pointSupportWindowRestrictionDiagramIso (K : DM(k)) (n : ℤ)
    (x : ConiveauPoints k X p) :
    pointSupportWindowIndices k X x ⋙ coniveauRelativeSupportDiagram k X K n p (p + 1) ≅
      pointSupportCohomologyDiagram k X K n x.1 := by
  refine NatIso.ofComponents (fun U ↦ pointSupportWindowRestrictionIso k X K n x U.unop) ?_
  intro U V i
  let H := effectivePairCohomology k K n
  let L := pointSupportWindowIndices k X x
  let W := coniveauSupportPairsInclusion k X p (p + 1)
  let P := pointSupportPairFunctor k X x.1
  let D := L ⋙ coniveauRelativeSupportDiagram k X K n p (p + 1)
  let G := pointSupportCohomologyDiagram k X K n x.1
  let m := W.map (L.map i).op
  let b := pointSupportWindowArrowMap k X x V.unop
  let c := P.map i.unop
  let d := pointSupportWindowArrowMap k X x U.unop
  let α : D.obj U ⟶ D.obj V := H.map m.op
  let β : D.obj V ⟶ G.obj V := H.map b.op
  let γ : D.obj U ⟶ G.obj U := H.map d.op
  let δ : G.obj U ⟶ G.obj V := H.map c.op
  have hα : D.map i = α := rfl
  have hβ : (pointSupportWindowRestrictionIso k X K n x V.unop).hom = β := rfl
  have hγ : (pointSupportWindowRestrictionIso k X K n x U.unop).hom = γ := rfl
  have hδ : G.map i = δ := rfl
  have h : b ≫ m = c ≫ d := pointSupportWindowArrowMap_naturality k X x i
  have hαβ : α ≫ β = γ ≫ δ := map_op_comp_eq H h
  exact (congrArg₂ (· ≫ ·) hα hβ).trans (hαβ.trans (congrArg₂ (· ≫ ·) hγ hδ).symm)

variable [UnivLE.{u, w'}]

attribute [local irreducible] effectivePairCohomology

private def pointSupportToWindowStage (K : DM(k)) (n : ℤ) (x : ConiveauPoints k X p)
    (U : (PointSupportNeighborhoods k X x.1)ᵒᵖ) :
    (pointSupportCohomologyDiagram k X K n x.1).obj U ⟶
      coniveauRelativeSupportCohomology k X K n p (p + 1) :=
  (pointSupportWindowRestrictionIso k X K n x U.unop).inv ≫
    colimit.ι (coniveauRelativeSupportDiagram k X K n p (p + 1))
      (pointSupportWindowIndex k X x U.unop)

private theorem pointSupportToWindowStage_naturality (K : DM(k)) (n : ℤ)
    (x : ConiveauPoints k X p) {U V : (PointSupportNeighborhoods k X x.1)ᵒᵖ} (i : U ⟶ V) :
    (pointSupportCohomologyDiagram k X K n x.1).map i ≫ pointSupportToWindowStage k X K n x V =
      pointSupportToWindowStage k X K n x U := by
  let L := pointSupportWindowIndices k X x
  let D := coniveauRelativeSupportDiagram k X K n p (p + 1)
  let G := pointSupportCohomologyDiagram k X K n x.1
  let e : D.obj (L.obj U) ≅ G.obj U := pointSupportWindowRestrictionIso k X K n x U.unop
  let e' : D.obj (L.obj V) ≅ G.obj V := pointSupportWindowRestrictionIso k X K n x V.unop
  let f := D.map (L.map i)
  let g := G.map i
  have hinv : g ≫ e'.inv = e.inv ≫ f :=
    (pointSupportWindowRestrictionDiagramIso k X K n x).inv.naturality i
  have hw : f ≫ colimit.ι D (L.obj V) = colimit.ι D (L.obj U) := colimit.w D (L.map i)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ colimit.ι D (L.obj V)) hinv).trans
      ((Category.assoc _ _ _).trans (congrArg (e.inv ≫ ·) hw)))

private def pointSupportWindowCocone (K : DM(k)) (n : ℤ) (x : ConiveauPoints k X p) :
    Cocone (pointSupportCohomologyDiagram k X K n x.1) :=
  coconeFromStages (pointSupportCohomologyDiagram k X K n x.1)
    (coniveauRelativeSupportCohomology k X K n p (p + 1))
    (pointSupportToWindowStage k X K n x) (pointSupportToWindowStage_naturality k X K n x)

/-- The canonical inclusion of the point support group in its coniveau window. -/
@[no_expose]
def pointSupportToConiveauWindow (K : DM(k)) (n : ℤ) (x : ConiveauPoints k X p) :
    pointSupportCohomology k X K n x.1 ⟶ coniveauRelativeSupportCohomology k X K n p (p + 1) :=
  colimit.desc (pointSupportCohomologyDiagram k X K n x.1) (pointSupportWindowCocone k X K n x)

/-- On a representative, the point inclusion first applies inverse open excision. -/
@[reassoc]
theorem pointSupportι_toConiveauWindow (K : DM(k)) (n : ℤ) (x : ConiveauPoints k X p)
    (U : PointSupportNeighborhoods k X x.1) :
    pointSupportι k X K n x.1 U ≫ pointSupportToConiveauWindow k X K n x =
      (pointSupportWindowRestrictionIso k X K n x U).inv ≫
        colimit.ι (coniveauRelativeSupportDiagram k X K n p (p + 1))
          (pointSupportWindowIndex k X x U) :=
  colimit.ι_desc (pointSupportWindowCocone k X K n x) (op U)

end AlgebraicGeometry.MotivicHomotopy

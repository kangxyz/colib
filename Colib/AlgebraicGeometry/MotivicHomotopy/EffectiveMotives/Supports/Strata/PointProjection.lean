/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata.PointWindow

/-! # The canonical point projections of the window -/

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

variable (X : Sm(k)) {p : ℕ}

local notation "Pairs" => ConiveauSupportPairs k X p (p + 1)
local notation "PairArrows" => coniveauSupportPairsInclusion k X p (p + 1)

/-- A neighbourhood restricts a window class to the closure of the given point whenever it
avoids the removed support and the complement of that closure avoids the larger support. -/
abbrev PointWindowNeighborhood {x : X.left} (ZW : Pairs)
    (U : PointSupportNeighborhoods k X x) : Prop :=
  U.1 ≤ ZW.1.1.1.compl ∧ pointSupportComplement k X x U.1 ≤ ZW.1.2.1.compl

/-- Every point admits a neighbourhood through which the window projection can be computed. -/
theorem exists_pointWindowNeighborhood (x : ConiveauPoints k X p) (ZW : Pairs) :
    ∃ U : PointSupportNeighborhoods k X x.1, PointWindowNeighborhood k X ZW U := by
  by_cases hx : x.1 ∈ (ZW.1.2.1 : Set X.left)
  · obtain ⟨U, hxU, hUZ, hcomp⟩ := Closeds.exists_open_isolating_pointClosure
      ZW.1.1.2 ZW.1.2.2 hx x.2
    exact ⟨⟨U, hxU⟩, hUZ, hcomp.le.trans inf_le_right⟩
  · exact ⟨⟨ZW.1.2.1.compl, hx⟩, Set.compl_subset_compl.mpr ZW.2, inf_le_left⟩

/-- Map of original pairs inducing the restriction from a window stage to a neighbourhood. -/
def pointWindowNeighborhoodArrowMap {x : X.left} (ZW : Pairs)
    (U : PointSupportNeighborhoods k X x) (hU : PointWindowNeighborhood k X ZW U) :
    pointSupportPair k X x U ⟶ (PairArrows).obj (op ZW) :=
  relativeOpenPairMap k X inf_le_left (Set.compl_subset_compl.mpr ZW.2) hU.2 hU.1

private theorem pointWindowNeighborhoodArrowMap_comp {x : X.left} {ZW : Pairs}
    {U V : PointSupportNeighborhoods k X x} (f : U ⟶ V)
    (hV : PointWindowNeighborhood k X ZW V) :
    (pointSupportPairFunctor k X x).map f ≫ pointWindowNeighborhoodArrowMap k X ZW V hV =
      pointWindowNeighborhoodArrowMap k X ZW U
        ⟨(show U.1 ≤ V.1 from f.le).trans hV.1,
          (inf_le_inf_right (Closeds.closure {x}).compl
            (show U.1 ≤ V.1 from f.le)).trans hV.2⟩ :=
  relativeOpenPairMap_comp k X _ _ _ _ _ _ _

private theorem pointWindowNeighborhoodArrowMap_transition {x : X.left} {ZW ZW' : Pairs}
    (f : ZW ⟶ ZW') (U : PointSupportNeighborhoods k X x)
    (hU : PointWindowNeighborhood k X ZW' U) :
    pointWindowNeighborhoodArrowMap k X ZW' U hU ≫ (PairArrows).map f.op =
      pointWindowNeighborhoodArrowMap k X ZW U
        ⟨hU.1.trans (Set.compl_subset_compl.mpr f.le.1),
          hU.2.trans (Set.compl_subset_compl.mpr f.le.2)⟩ :=
  relativeOpenPairMap_comp k X _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] effectivePairCohomology

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [UnivLE.{u, w'}]

local notation "DM(" field ")" => EffectiveMotivesMinus field

variable (K : DM(k)) (n : ℤ)

local notation "D" => coniveauRelativeSupportDiagram k X K n p (p + 1)
local notation "H" => effectivePairCohomology k K n

/-- The restriction from a stage of the window to the point group through any isolating open. -/
def pointWindowProjectionThrough (x : X.left) (ZW : Pairs)
    (U : PointSupportNeighborhoods k X x) (hU : PointWindowNeighborhood k X ZW U) :
    (D).obj ZW ⟶ pointSupportCohomology k X K n x :=
  (H).map (pointWindowNeighborhoodArrowMap k X ZW U hU).op ≫ pointSupportι k X K n x U

private theorem pointWindowProjectionThrough_eq_of_le (x : X.left) (ZW : Pairs)
    {U V : PointSupportNeighborhoods k X x} (f : U ⟶ V)
    (hV : PointWindowNeighborhood k X ZW V) :
    pointWindowProjectionThrough k X K n x ZW V hV =
      pointWindowProjectionThrough k X K n x ZW U
        ⟨(show U.1 ≤ V.1 from f.le).trans hV.1,
          (inf_le_inf_right (Closeds.closure {x}).compl
            (show U.1 ≤ V.1 from f.le)).trans hV.2⟩ := by
  let G := pointSupportCohomologyDiagram k X K n x
  let hU : PointWindowNeighborhood k X ZW U :=
    ⟨(show U.1 ≤ V.1 from f.le).trans hV.1,
      (inf_le_inf_right (Closeds.closure {x}).compl (show U.1 ≤ V.1 from f.le)).trans hV.2⟩
  let a := pointWindowNeighborhoodArrowMap k X ZW V hV
  let b := (pointSupportPairFunctor k X x).map f
  let c := pointWindowNeighborhoodArrowMap k X ZW U hU
  let a' : (D).obj ZW ⟶ G.obj (op V) := (H).map a.op
  let b' : G.obj (op V) ⟶ G.obj (op U) := (H).map b.op
  let c' : (D).obj ZW ⟶ G.obj (op U) := (H).map c.op
  have h : b ≫ a = c := pointWindowNeighborhoodArrowMap_comp k X f hV
  have hc : a' ≫ b' = c' :=
    ((H).map_comp a.op b.op).symm.trans ((H).congr_map (congrArg Quiver.Hom.op h))
  have hw : b' ≫ colimit.ι G (op U) = colimit.ι G (op V) := colimit.w G f.op
  exact (congrArg (a' ≫ ·) hw).symm.trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ colimit.ι G (op U)) hc))

/-- The restriction to the point group is independent of the isolating open. -/
theorem pointWindowProjectionThrough_eq (x : X.left) (ZW : Pairs)
    (U V : PointSupportNeighborhoods k X x)
    (hU : PointWindowNeighborhood k X ZW U) (hV : PointWindowNeighborhood k X ZW V) :
    pointWindowProjectionThrough k X K n x ZW U hU =
      pointWindowProjectionThrough k X K n x ZW V hV :=
  (pointWindowProjectionThrough_eq_of_le k X K n x ZW (OpenNhds.infLELeft U V) hU).trans
    (pointWindowProjectionThrough_eq_of_le k X K n x ZW (OpenNhds.infLERight U V) hV).symm

private def pointWindowStageProjection (x : ConiveauPoints k X p) (ZW : Pairs) :
    (D).obj ZW ⟶ pointSupportCohomology k X K n x.1 :=
  let h := exists_pointWindowNeighborhood k X x ZW
  pointWindowProjectionThrough k X K n x.1 ZW h.choose h.choose_spec

private theorem pointWindowStageProjection_eq (x : ConiveauPoints k X p) (ZW : Pairs)
    (U : PointSupportNeighborhoods k X x.1) (hU : PointWindowNeighborhood k X ZW U) :
    pointWindowStageProjection k X K n x ZW = pointWindowProjectionThrough k X K n x.1 ZW U hU :=
  pointWindowProjectionThrough_eq k X K n x.1 ZW _ U _ hU

private theorem pointWindowStageProjection_naturality (x : ConiveauPoints k X p)
    {ZW ZW' : Pairs} (f : ZW ⟶ ZW') :
    (D).map f ≫ pointWindowStageProjection k X K n x ZW' =
      pointWindowStageProjection k X K n x ZW := by
  let U := (exists_pointWindowNeighborhood k X x ZW').choose
  let hU := (exists_pointWindowNeighborhood k X x ZW').choose_spec
  let hU₀ : PointWindowNeighborhood k X ZW U :=
    ⟨hU.1.trans (Set.compl_subset_compl.mpr f.le.1),
      hU.2.trans (Set.compl_subset_compl.mpr f.le.2)⟩
  let G := pointSupportCohomologyDiagram k X K n x.1
  let a := (PairArrows).map f.op
  let b := pointWindowNeighborhoodArrowMap k X ZW' U hU
  let c := pointWindowNeighborhoodArrowMap k X ZW U hU₀
  let a' : (D).obj ZW ⟶ (D).obj ZW' := (H).map a.op
  let b' : (D).obj ZW' ⟶ G.obj (op U) := (H).map b.op
  let c' : (D).obj ZW ⟶ G.obj (op U) := (H).map c.op
  have ha : (D).map f = a' := rfl
  have h : b ≫ a = c := pointWindowNeighborhoodArrowMap_transition k X f U hU
  have hc : a' ≫ b' = c' :=
    ((H).map_comp a.op b.op).symm.trans ((H).congr_map (congrArg Quiver.Hom.op h))
  have h₁ : pointWindowStageProjection k X K n x ZW' = b' ≫ colimit.ι G (op U) :=
    pointWindowStageProjection_eq k X K n x ZW' U hU
  have h₂ : pointWindowStageProjection k X K n x ZW = c' ≫ colimit.ι G (op U) :=
    pointWindowStageProjection_eq k X K n x ZW U hU₀
  exact (congrArg₂ (· ≫ ·) ha h₁).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ colimit.ι G (op U)) hc).trans h₂.symm))

private def coconeFromProjections {A C : Type*} [Category* A] [Category* C]
    (F : A ⥤ C) (B : C) (q : ∀ a, F.obj a ⟶ B)
    (hq : ∀ {a b : A} (f : a ⟶ b), F.map f ≫ q b = q a) : Cocone F where
  pt := B
  ι := { app := q, naturality := fun a _ f ↦ (hq f).trans (Category.comp_id (q a)).symm }

private def pointWindowProjectionCocone (x : ConiveauPoints k X p) : Cocone (D) :=
  coconeFromProjections (D) (pointSupportCohomology k X K n x.1)
    (pointWindowStageProjection k X K n x) (pointWindowStageProjection_naturality k X K n x)

/-- The projection of the coniveau window to the indicated point group. -/
@[no_expose]
def coniveauWindowPointProjection (x : ConiveauPoints k X p) :
    coniveauRelativeSupportCohomology k X K n p (p + 1) ⟶
      pointSupportCohomology k X K n x.1 :=
  colimit.desc (D) (pointWindowProjectionCocone k X K n x)

/-- Stage formula for the point projection. -/
@[reassoc]
theorem ι_coniveauWindowPointProjection (x : ConiveauPoints k X p) (ZW : Pairs)
    (U : PointSupportNeighborhoods k X x.1) (hU : PointWindowNeighborhood k X ZW U) :
    colimit.ι (D) ZW ≫ coniveauWindowPointProjection k X K n x =
      pointWindowProjectionThrough k X K n x.1 ZW U hU :=
  (colimit.ι_desc (pointWindowProjectionCocone k X K n x) ZW).trans
    (pointWindowStageProjection_eq k X K n x ZW U hU)

/-- A stage supported away from the indicated point has zero projection there. -/
@[reassoc]
theorem ι_coniveauWindowPointProjection_eq_zero (x : ConiveauPoints k X p) (ZW : Pairs)
    (hx : x.1 ∉ (ZW.1.2.1 : Set X.left)) :
    colimit.ι (D) ZW ≫ coniveauWindowPointProjection k X K n x = 0 := by
  let B := ZW.1.2.1.compl
  let U : PointSupportNeighborhoods k X x.1 := ⟨B, hx⟩
  let hU : PointWindowNeighborhood k X ZW U := ⟨Set.compl_subset_compl.mpr ZW.2, inf_le_left⟩
  rw [ι_coniveauWindowPointProjection k X K n x ZW U hU]
  let a := relativeOpenPairMap k X (inf_le_left : pointSupportComplement k X x.1 U.1 ≤ U.1)
    (le_rfl : B ≤ B) inf_le_left le_rfl
  let b := relativeOpenPairMap k X (le_rfl : B ≤ B) (Set.compl_subset_compl.mpr ZW.2)
    le_rfl hU.1
  have hab : a ≫ b = pointWindowNeighborhoodArrowMap k X ZW U hU :=
    relativeOpenPairMap_comp k X _ _ _ _ _ _ _
  let G := pointSupportCohomologyDiagram k X K n x.1
  let M := (H).obj (op (relativeOpenPair k X (le_rfl : B ≤ B)))
  let a' : M ⟶ G.obj (op U) := (H).map a.op
  let b' : (D).obj ZW ⟶ M := (H).map b.op
  let c' : (D).obj ZW ⟶ G.obj (op U) := (H).map (pointWindowNeighborhoodArrowMap k X ZW U hU).op
  have hc : b' ≫ a' = c' :=
    ((H).map_comp b.op a.op).symm.trans ((H).congr_map (congrArg Quiver.Hom.op hab))
  have hz : IsZero M := isZero_relativeOpenPairCohomology_refl k X K n B
  have hzero : c' = 0 := hc.symm.trans
    ((congrArg (b' ≫ ·) (hz.eq_of_src a' 0)).trans comp_zero)
  exact (congrArg (· ≫ colimit.ι G (op U)) hzero).trans zero_comp

/-- The inclusion and projection at the same point compose to the identity. -/
@[reassoc (attr := simp)]
theorem pointSupportToConiveauWindow_projection_self (x : ConiveauPoints k X p) :
    pointSupportToConiveauWindow k X K n x ≫ coniveauWindowPointProjection k X K n x = 𝟙 _ := by
  apply colimit.hom_ext
  intro U
  let ZW := pointSupportWindowIndex k X x U.unop
  have hU : PointWindowNeighborhood k X ZW U.unop := by
    refine ⟨?_, inf_le_right⟩
    exact le_sup_right.trans (pointSupportWindow_cover k X x U.unop).le
  let G := pointSupportCohomologyDiagram k X K n x.1
  let e := pointSupportWindowRestrictionIso k X K n x U.unop
  let a := pointSupportToConiveauWindow k X K n x
  let b := coniveauWindowPointProjection k X K n x
  have ha : colimit.ι G U ≫ a = e.inv ≫ colimit.ι (D) ZW :=
    pointSupportι_toConiveauWindow k X K n x U.unop
  have hb : colimit.ι (D) ZW ≫ b = e.hom ≫ colimit.ι G U :=
    ι_coniveauWindowPointProjection k X K n x ZW U.unop hU
  calc
    _ = (e.inv ≫ colimit.ι (D) ZW) ≫ b :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ b) ha)
    _ = e.inv ≫ e.hom ≫ colimit.ι G U :=
      (Category.assoc _ _ _).trans (congrArg (e.inv ≫ ·) hb)
    _ = _ := (e.inv_hom_id_assoc _).trans (Category.comp_id _).symm

/-- A point included into its window projects to zero at any other point of that codimension. -/
@[reassoc]
theorem pointSupportToConiveauWindow_projection_of_ne {x y : ConiveauPoints k X p} (hxy : x ≠ y) :
    pointSupportToConiveauWindow k X K n x ≫ coniveauWindowPointProjection k X K n y = 0 := by
  have hy : y.1 ∉ closure ({x.1} : Set X.left) := by
    intro hyx
    have hc := Closeds.succ_le_coheight_of_mem_pointClosure hyx
      (fun h ↦ hxy (Subtype.ext h.symm)) x.2.ge
    rw [y.2, ENat.natCast_le_natCast] at hc
    exact (Nat.not_succ_le_self _) hc
  apply colimit.hom_ext
  intro U
  let G := pointSupportCohomologyDiagram k X K n x.1
  let ZW := pointSupportWindowIndex k X x U.unop
  let e := pointSupportWindowRestrictionIso k X K n x U.unop
  let a := pointSupportToConiveauWindow k X K n x
  let b := coniveauWindowPointProjection k X K n y
  have ha : colimit.ι G U ≫ a = e.inv ≫ colimit.ι (D) ZW :=
    pointSupportι_toConiveauWindow k X K n x U.unop
  have hb : colimit.ι (D) ZW ≫ b = 0 :=
    ι_coniveauWindowPointProjection_eq_zero k X K n y ZW hy
  calc
    _ = (e.inv ≫ colimit.ι (D) ZW) ≫ b :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ b) ha)
    _ = e.inv ≫ 0 := (Category.assoc _ _ _).trans (congrArg (e.inv ≫ ·) hb)
    _ = _ := comp_zero.trans comp_zero.symm

end AlgebraicGeometry.MotivicHomotopy

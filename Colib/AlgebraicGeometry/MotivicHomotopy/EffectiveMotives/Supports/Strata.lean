/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata.DisjointCover
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata.PointProjection
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import StacksFrontier.Algebra.Category.Grp.DirectSumCoproduct

/-! # The codimension stratum of the coniveau tower -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

attribute [local instance] specializationOrder Classical.decEq

private theorem abelianCoproduct_ext {I : Type u} [UnivLE.{u, w'}] [DecidableEq I]
    (A : I → AddCommGrpCat.{w'}) (a b : ↥(∐ A))
    (h : ∀ i, Sigma.π A i a = Sigma.π A i b) : a = b := by
  classical
  let e : I ≃ Shrink.{w'} I := equivShrink I
  let B (j : Shrink.{w'} I) := A (e.symm j)
  let E := Sigma.whiskerEquiv (f := B) (g := A) e.symm (fun j ↦ Iso.refl (B j))
  let d := AddCommGrpCat.directSumCoproductIso B
  let f := d ≪≫ E
  let c := AddCommGrpCat.directSumCofan B
  let hc := AddCommGrpCat.directSumCofanIsColimit B
  have hι (i : Shrink.{w'} I) : c.inj i ≫ f.hom = Sigma.ι A (e.symm i) := by
    rw [Iso.trans_hom, ← Category.assoc, AddCommGrpCat.inj_directSumCoproductIso_hom,
      Sigma.whiskerEquiv_hom, Sigma.map', Sigma.ι_comp_desc, Iso.refl_inv, Category.id_comp]
  let v (j : Shrink.{w'} I) : c.pt ⟶ B j :=
    AddCommGrpCat.ofHom (DFinsupp.evalAddMonoidHom (β := fun t ↦ (B t : Type w')) j)
  have hproj (j : Shrink.{w'} I) : f.hom ≫ Sigma.π A (e.symm j) = v j := by
    apply Cofan.IsColimit.hom_ext hc
    intro t
    rw [← Category.assoc, hι]
    by_cases ht : t = j
    · subst t
      rw [Sigma.ι_π_eq_id]
      apply AddCommGrpCat.hom_ext
      ext x
      change x = (DFinsupp.single (β := fun t ↦ (B t : Type w')) j x) j
      rw [DFinsupp.single_eq_same]
    · rw [Sigma.ι_π_of_ne _ (e.symm.injective.ne ht)]
      apply AddCommGrpCat.hom_ext
      ext x
      change (0 : B j) = (DFinsupp.single (β := fun t ↦ (B t : Type w')) t x) j
      rw [DFinsupp.single_eq_of_ne (Ne.symm ht)]
  apply (AddCommGrpCat.mono_iff_injective f.inv).mp inferInstance
  apply DFinsupp.ext
  intro j
  change v j (f.inv a) = v j (f.inv b)
  rw [← hproj]
  exact (congrArg (Sigma.π A (e.symm j)) (f.inv_hom_id_apply a)).trans
    ((h _).trans (congrArg (Sigma.π A (e.symm j)) (f.inv_hom_id_apply b)).symm)

private theorem sum_of_stage_maps {I : Type u} [Fintype I] {M : AddCommGrpCat.{w'}}
    {A B : I → AddCommGrpCat.{w'}} (a : ∀ i, A i ⟶ M) (b : ∀ i, M ⟶ B i)
    (e : ∀ i, A i ≅ B i) (hdiag : ∀ i, a i ≫ b i = (e i).hom)
    (hzero : ∀ i j, i ≠ j → a i ≫ b j = 0)
    (hsep : ∀ x y : M, (∀ i, b i x = b i y) → x = y) (r : M) :
    (∑ i, a i ((e i).inv (b i r))) = r := by
  classical
  apply hsep
  intro j
  rw [map_sum, Finset.sum_eq_single j]
  · change (a j ≫ b j) ((e j).inv (b j r)) = _
    rw [hdiag]
    exact (e j).inv_hom_id_apply _
  · intro i _ hij
    change (a i ≫ b j) ((e i).inv (b i r)) = 0
    simp only [hzero i j hij, AddCommGrpCat.zero_apply]
  · simp

private theorem lift_stage_sum {I J : Type u} [Fintype I] [UnivLE.{u, w'}]
    (A : J → AddCommGrpCat.{w'}) (j : I → J) (L : I → AddCommGrpCat.{w'})
    {B W : AddCommGrpCat.{w'}} (ι : ∀ i, L i ⟶ A (j i)) (d : ∀ i, L i ⟶ B)
    (q : ∀ a, A a ⟶ W) (f : B ⟶ W) (h : ∀ i, ι i ≫ q (j i) = d i ≫ f)
    (s : ∀ i, L i) (r : B) (hr : (∑ i, d i (s i)) = r) :
    ∃ a : ↥(∐ A), Sigma.desc q a = f r := by
  let z (i : I) := Sigma.ι A (j i) (ι i (s i))
  have hz (i : I) : Sigma.desc q (z i) = f (d i (s i)) := by
    have hj : Sigma.ι A (j i) ≫ Sigma.desc q = q (j i) := Sigma.ι_comp_desc _ _
    exact ConcreteCategory.congr_hom ((congrArg (ι i ≫ ·) hj).trans (h i)) (s i)
  refine ⟨∑ i, z i, ?_⟩
  calc
    Sigma.desc q (∑ i, z i) = ∑ i, Sigma.desc q (z i) := map_sum _ _ _
    _ = ∑ i, f (d i (s i)) := Finset.sum_congr rfl (fun i _ ↦ hz i)
    _ = f (∑ i, d i (s i)) := (map_sum _ _ _).symm
    _ = f r := congrArg f hr

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable (X : Sm(k))

section StageGeometry

variable (p : ℕ)

local notation "Pairs" => ConiveauSupportPairs k X p (p + 1)

private abbrev StagePoints (ZW : Pairs) :=
  {x : X.left // x ∈ (ZW.1.2.1 : Set X.left) ∧ coheight x = p}

private abbrev stagePoint (ZW : Pairs) (i : StagePoints k X p ZW) : ConiveauPoints k X p :=
  ⟨i.1, i.2.2⟩

private theorem stagePointClosure_le (ZW : Pairs) (i : StagePoints k X p ZW) :
    Closeds.closure {i.1} ≤ ZW.1.2.1 :=
  closure_minimal (Set.singleton_subset_iff.mpr i.2.1) ZW.1.2.1.isClosed

private def stagePointOpen (ZW : Pairs) (i : StagePoints k X p ZW) :
    PointSupportNeighborhoods k X i.1 := ⟨ZW.1.1.1.compl, by
  intro hi
  have h := ZW.1.1.2 i.1 hi
  rw [i.2.2, ENat.natCast_le_natCast] at h
  exact (Nat.not_succ_le_self _) h⟩

private def stageToPointArrow (ZW : Pairs) (i : StagePoints k X p ZW) :
    (coniveauSupportPairsInclusion k X p (p + 1)).obj (op ZW) ⟶
      pointSupportPair k X i.1 (stagePointOpen k X p ZW i) := by
  let B := ZW.1.2.1.compl
  let U := ZW.1.1.1.compl
  let C := Closeds.closure {i.1}
  let h : B ≤ U := Set.compl_subset_compl.mpr ZW.2
  exact relativeOpenPairMap k X h (inf_le_left : U ⊓ C.compl ≤ U)
    (le_inf h (Set.compl_subset_compl.mpr (stagePointClosure_le k X p ZW i))) le_rfl

private abbrev stagePointIndex (ZW : Pairs) (i : StagePoints k X p ZW) : Pairs :=
  pointSupportWindowIndex k X (stagePoint k X p ZW i) (stagePointOpen k X p ZW i)

private def stagePointIndexMap (ZW : Pairs) (i : StagePoints k X p ZW) :
    stagePointIndex k X p ZW i ⟶ ZW := by
  refine homOfLE ⟨?_, stagePointClosure_le k X p ZW i⟩
  change Closeds.closure {i.1} ⊓ ZW.1.1.1.compl.compl ≤ ZW.1.1.1
  exact inf_le_right.trans (Closeds.compl_compl ZW.1.1.1).le

private theorem stagePointIndexMap_arrow (ZW : Pairs) (i : StagePoints k X p ZW) :
    (coniveauSupportPairsInclusion k X p (p + 1)).map (stagePointIndexMap k X p ZW i).op =
      stageToPointArrow k X p ZW i ≫ pointSupportWindowArrowMap k X (stagePoint k X p ZW i)
        (stagePointOpen k X p ZW i) := by
  let U := ZW.1.1.1.compl
  let C := Closeds.closure {i.1}
  let O := SmoothSite.opensFunctor X
  let j := stagePointIndexMap k X p ZW i
  let hl := Set.compl_subset_compl.mpr (stagePointClosure_le k X p ZW i)
  let hr := Set.compl_subset_compl.mpr j.le.1
  apply Arrow.hom_ext
  · change O.map (homOfLE hl) = O.map (homOfLE (le_inf (Set.compl_subset_compl.mpr ZW.2) hl)) ≫
      O.map (homOfLE (inf_le_right : U ⊓ C.compl ≤ C.compl))
    rw [← O.map_comp]
    exact congrArg O.map (Subsingleton.elim _ _)
  · change O.map (homOfLE hr) = O.map (homOfLE (le_rfl : U ≤ U)) ≫ O.map (homOfLE hr)
    rw [← O.map_comp]
    exact congrArg O.map (Subsingleton.elim _ _)

private abbrev stageOpenArrow (ZW : Pairs) {V : X.left.Opens}
    (hB : ZW.1.2.1.compl ≤ V) (hV : V ≤ ZW.1.1.1.compl) :=
  relativeOpenPairMap k X hB (Set.compl_subset_compl.mpr ZW.2) le_rfl hV

end StageGeometry

private theorem representedOpenCofan_restrictions_injective {C : Type*}
    [Category.{w'} C] [Preadditive C] {I : Type u} {B U : X.left.Opens}
    (M : Arrow Sm(k) ⥤ C) (R : (Arrow Sm(k))ᵒᵖ ⥤ AddCommGrpCat.{w'}) (K₀ : C)
    (hR : R = M.op ⋙ preadditiveYoneda.obj K₀) (hB : B ≤ U) (V : I → X.left.Opens)
    (hb : ∀ j, B ≤ V j) (hu : ∀ j, V j ≤ U)
    (hc : IsColimit (relativeOpenCofan k X hB V hb hu M))
    (a b : R.obj (op (relativeOpenPair k X hB)))
    (h : ∀ j, R.map (relativeOpenPairMap k X (hb j) hB le_rfl (hu j)).op a =
      R.map (relativeOpenPairMap k X (hb j) hB le_rfl (hu j)).op b) : a = b := by
  subst R
  exact hc.hom_ext (fun ⟨j⟩ ↦ h j)

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "DM(" field ")" => EffectiveMotivesMinus field

variable (K : DM(k)) (n : ℤ) (p : ℕ)

local notation "Pairs" => ConiveauSupportPairs k X p (p + 1)
local notation "D" => coniveauRelativeSupportDiagram k X K n p (p + 1)
local notation "H" => effectivePairCohomology k K n
set_option quotPrecheck false in
local notation "G" => fun x : ConiveauPoints k X p ↦ pointSupportCohomology k X K n x.1

private theorem representedStageCohomologyFactor :
    (H) = (effectivePairMotiveFunctor k).op ⋙ preadditiveYoneda.obj (K⟦n⟧) := rfl

attribute [local irreducible] effectivePairCohomology

private abbrev stagePointGroup (ZW : Pairs) (i : StagePoints k X p ZW) : AddCommGrpCat.{w'} :=
  (pointSupportCohomologyDiagram k X K n i.1).obj (op (stagePointOpen k X p ZW i))

private def stagePointMap (ZW : Pairs) (i : StagePoints k X p ZW) :
    stagePointGroup k X K n p ZW i ⟶ (D).obj ZW :=
  (H).map (stageToPointArrow k X p ZW i).op

private def stageOpenMap (ZW : Pairs) {V : X.left.Opens}
    (hB : ZW.1.2.1.compl ≤ V) (hV : V ≤ ZW.1.1.1.compl) :
    (D).obj ZW ⟶ (H).obj (op (relativeOpenPair k X hB)) :=
  (H).map (stageOpenArrow k X p ZW hB hV).op

private def stageCoverIsColimit (ZW : Pairs) [Finite (StagePoints k X p ZW)]
    (V : StagePoints k X p ZW → X.left.Opens)
    (hBV : ∀ i, ZW.1.2.1.compl ≤ V i) (hVU : ∀ i, V i ≤ ZW.1.1.1.compl)
    (hcover : ZW.1.1.1.compl ≤ ZW.1.2.1.compl ⊔ iSup V)
    (hinter : ∀ i j, i ≠ j → V i ⊓ V j ≤ ZW.1.2.1.compl) :
    IsColimit (relativeOpenCofan k X (Set.compl_subset_compl.mpr ZW.2) V hBV hVU
      (effectivePairMotiveFunctor k)) :=
  effectiveRelativeOpenCofanIsColimit k X (Set.compl_subset_compl.mpr ZW.2)
    V hBV hVU hcover hinter

set_option maxHeartbeats 500000 in
-- The represented separation theorem specializes to the effective motive of the stage pair.
private theorem stageCover_separates (ZW : Pairs) [Finite (StagePoints k X p ZW)]
    (V : StagePoints k X p ZW → X.left.Opens)
    (hBV : ∀ i, ZW.1.2.1.compl ≤ V i) (hVU : ∀ i, V i ≤ ZW.1.1.1.compl)
    (hcover : ZW.1.1.1.compl ≤ ZW.1.2.1.compl ⊔ iSup V)
    (hinter : ∀ i j, i ≠ j → V i ⊓ V j ≤ ZW.1.2.1.compl)
    (a b : (D).obj ZW)
    (h : ∀ i, stageOpenMap k X K n p ZW (hBV i) (hVU i) a =
      stageOpenMap k X K n p ZW (hBV i) (hVU i) b) : a = b := by
  let hB : ZW.1.2.1.compl ≤ ZW.1.1.1.compl := Set.compl_subset_compl.mpr ZW.2
  let M : Arrow Sm(k) ⥤ DM(k) := effectivePairMotiveFunctor k
  let R : (Arrow Sm(k))ᵒᵖ ⥤ AddCommGrpCat.{w'} := (H)
  let K₀ : DM(k) := K⟦n⟧
  have hR : R = M.op ⋙ preadditiveYoneda.obj K₀ := representedStageCohomologyFactor k K n
  let hc : IsColimit (relativeOpenCofan k X hB V hBV hVU M) :=
    stageCoverIsColimit k X p ZW V hBV hVU hcover hinter
  let Q := relativeOpenPair k X hB
  let a' : R.obj (op Q) := a
  let b' : R.obj (op Q) := b
  have h' : ∀ j, R.map (relativeOpenPairMap k X (hBV j) hB le_rfl (hVU j)).op a' =
      R.map (relativeOpenPairMap k X (hBV j) hB le_rfl (hVU j)).op b' := h
  have hab : a' = b' := representedOpenCofan_restrictions_injective k X M R K₀ hR hB V
    hBV hVU hc a' b' h'
  exact hab

private theorem map_comp_stageToPointArrow_eq_zero (ZW : Pairs)
    (i : StagePoints k X p ZW) {V : X.left.Opens}
    (hB : ZW.1.2.1.compl ≤ V) (hV : V ≤ ZW.1.1.1.compl)
    (h : V ≤ ZW.1.1.1.compl ⊓ (Closeds.closure {i.1}).compl) :
    stagePointMap k X K n p ZW i ≫ stageOpenMap k X K n p ZW hB hV = 0 := by
  let B := ZW.1.2.1.compl
  let U := ZW.1.1.1.compl
  let C := Closeds.closure {i.1}
  let hBW : B ≤ U := Set.compl_subset_compl.mpr ZW.2
  let hC : U ⊓ C.compl ≤ U := inf_le_left
  let hBC : B ≤ U ⊓ C.compl := le_inf hBW
    (Set.compl_subset_compl.mpr (stagePointClosure_le k X p ZW i))
  let d := stageToPointArrow k X p ZW i
  let b := relativeOpenPairMap k X hB hBW le_rfl hV
  let f := relativeOpenPairMap k X hB (le_rfl : V ≤ V) hB le_rfl
  let g := relativeOpenPairMap k X (le_rfl : V ≤ V) hC h hV
  have hfg : b ≫ d = f ≫ g :=
    (relativeOpenPairMap_comp k X hB hBW hC le_rfl hV hBC le_rfl).trans
      (relativeOpenPairMap_comp k X hB (le_rfl : V ≤ V) hC hB le_rfl h hV).symm
  let O := (D).obj ZW
  let L := stagePointGroup k X K n p ZW i
  let M := (H).obj (op (relativeOpenPair k X (le_rfl : V ≤ V)))
  let N := (H).obj (op (relativeOpenPair k X hB))
  let d' : L ⟶ O := stagePointMap k X K n p ZW i
  let b' : O ⟶ N := stageOpenMap k X K n p ZW hB hV
  let f' : M ⟶ N := (H).map f.op
  let g' : L ⟶ M := (H).map g.op
  have he : d' ≫ b' = g' ≫ f' := ((H).map_comp d.op b.op).symm.trans
    (((H).congr_map (congrArg Quiver.Hom.op hfg)).trans ((H).map_comp g.op f.op))
  have hz : IsZero M := isZero_relativeOpenPairCohomology_refl k X K n V
  exact he.trans ((congrArg (g' ≫ ·) (hz.eq_of_src f' 0)).trans comp_zero)

private theorem stage_is_sum_of_point_classes (ZW : Pairs) [Fintype (StagePoints k X p ZW)]
    (V : StagePoints k X p ZW → X.left.Opens)
    (hBV : ∀ i, ZW.1.2.1.compl ≤ V i) (hVU : ∀ i, V i ≤ ZW.1.1.1.compl)
    (hcover : ZW.1.1.1.compl ≤ ZW.1.2.1.compl ⊔ iSup V)
    (hinter : ∀ i j, i ≠ j → V i ⊓ V j ≤ ZW.1.2.1.compl)
    (hComp : ∀ i, V i ⊓ (Closeds.closure {i.1}).compl = ZW.1.2.1.compl)
    (hEx : ∀ i, ZW.1.1.1.compl ⊓ (Closeds.closure {i.1}).compl ⊔ V i = ZW.1.1.1.compl)
    (r : (D).obj ZW) :
    ∃ s : ∀ i : StagePoints k X p ZW, stagePointGroup k X K n p ZW i,
      (∑ i, stagePointMap k X K n p ZW i (s i)) = r := by
  classical
  let Z := ZW.1.1.1
  let W := ZW.1.2.1
  let U := Z.compl
  let B := W.compl
  let hBW : B ≤ U := Set.compl_subset_compl.mpr ZW.2
  let I := StagePoints k X p ZW
  let Bx (i : I) := U ⊓ (Closeds.closure {i.1}).compl
  let b (i : I) := relativeOpenPairMap k X (hBV i) hBW le_rfl (hVU i)
  let d (i : I) := stageToPointArrow k X p ZW i
  let q (i : I) := relativeOpenPairMap k X (hBV i) (inf_le_left : Bx i ≤ U)
    (le_inf hBW (Set.compl_subset_compl.mpr (stagePointClosure_le k X p ZW i))) (hVU i)
  have hq (i : I) : b i ≫ d i = q i := relativeOpenPairMap_comp k X _ _ _ _ _ _ _
  have hs (i : I) : IsIso ((H).map (q i).op) := by
    have hh : B = V i ⊓ Bx i := by
      rw [show Bx i = U ⊓ (Closeds.closure {i.1}).compl from rfl, ← inf_assoc,
        inf_eq_left.mpr (hVU i)]
      exact (hComp i).symm
    exact isIso_relativeOpenPairCohomology_openExcision_of_eq k X K n _ _ _ _ hh (hEx i)
  let O := (D).obj ZW
  let L (i : I) := stagePointGroup k X K n p ZW i
  let M (i : I) := (H).obj (op (relativeOpenPair k X (hBV i)))
  let d' (i : I) : L i ⟶ O := stagePointMap k X K n p ZW i
  let b' (i : I) : O ⟶ M i := stageOpenMap k X K n p ZW (hBV i) (hVU i)
  let e (i : I) : L i ≅ M i := @asIso AddCommGrpCat.{w'} _ _ _ ((H).map (q i).op) (hs i)
  have hdiag (i : I) : d' i ≫ b' i = (e i).hom :=
    ((H).map_comp (d i).op (b i).op).symm.trans ((H).congr_map (congrArg Quiver.Hom.op (hq i)))
  have hoffdiag (i j : I) (hij : i ≠ j) : d' i ≫ b' j = 0 := by
    refine map_comp_stageToPointArrow_eq_zero k X K n p ZW i (hBV j) (hVU j) (le_inf (hVU j) ?_)
    intro y hyj hyi
    have hyU := hVU j hyj
    have hyV : y ∈ V i := by
      have hy := (hEx i).ge hyU
      exact hy.resolve_left (fun hb ↦ hb.2 hyi)
    exact (hinter i j hij ⟨hyV, hyj⟩) (stagePointClosure_le k X p ZW i hyi)
  have hsep (r s : O) (h : ∀ i, b' i r = b' i s) : r = s :=
    stageCover_separates k X K n p ZW V hBV hVU hcover hinter r s h
  exact ⟨fun i ↦ (e i).inv (b' i r), sum_of_stage_maps d' b' e hdiag hoffdiag hsep r⟩

variable [UnivLE.{u, w'}]

private theorem stagePoint_map_to_window (ZW : Pairs) (i : StagePoints k X p ZW) :
    pointSupportι k X K n i.1 (stagePointOpen k X p ZW i) ≫
        pointSupportToConiveauWindow k X K n (stagePoint k X p ZW i) =
      stagePointMap k X K n p ZW i ≫ colimit.ι (D) ZW := by
  let x := stagePoint k X p ZW i
  let V := stagePointOpen k X p ZW i
  let B := stagePointGroup k X K n p ZW i
  let ZW₀ := stagePointIndex k X p ZW i
  let j := stagePointIndexMap k X p ZW i
  let E : (D).obj ZW₀ ≅ B := pointSupportWindowRestrictionIso k X K n x V
  let m := pointSupportWindowArrowMap k X x V
  let d := stageToPointArrow k X p ZW i
  let g : (D).obj ZW₀ ⟶ B := (H).map m.op
  let h : B ⟶ (D).obj ZW := stagePointMap k X K n p ZW i
  let T := coniveauSupportPairsInclusion k X p (p + 1)
  let j' : (D).obj ZW₀ ⟶ (D).obj ZW := (H).map ((T).map j.op).op
  have hg : E.hom = g := rfl
  have hj : (D).map j = j' := rfl
  have hw := stagePointIndexMap_arrow k X p ZW i
  have hj' : j' = g ≫ h := ((H).congr_map (congrArg Quiver.Hom.op hw)).trans
    ((H).map_comp m.op d.op)
  have hE : E.inv ≫ (D).map j = h := (E.inv_comp_eq).2
    (hj.trans (hj'.trans (congrArg (· ≫ h) hg.symm)))
  calc
    _ = E.inv ≫ colimit.ι (D) ZW₀ := pointSupportι_toConiveauWindow k X K n x V
    _ = E.inv ≫ (D).map j ≫ colimit.ι (D) ZW :=
      congrArg (E.inv ≫ ·) (colimit.w (D) j).symm
    _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ colimit.ι (D) ZW) hE)

private theorem stage_sum_maps_to_point_sum (ZW : Pairs) [Fintype (StagePoints k X p ZW)]
    (s : ∀ i : StagePoints k X p ZW, stagePointGroup k X K n p ZW i) (r : (D).obj ZW)
    (hs : (∑ i, stagePointMap k X K n p ZW i (s i)) = r) :
    ∃ a : ↥(∐ (G)), Sigma.desc (pointSupportToConiveauWindow k X K n) a = colimit.ι (D) ZW r :=
  lift_stage_sum (G) (stagePoint k X p ZW) (stagePointGroup k X K n p ZW)
    (fun i ↦ pointSupportι k X K n i.1 (stagePointOpen k X p ZW i))
    (stagePointMap k X K n p ZW) (pointSupportToConiveauWindow k X K n) (colimit.ι (D) ZW)
    (stagePoint_map_to_window k X K n p ZW) s r hs

private theorem stage_generates (ZW : Pairs)
    (hgood : ∀ y ∈ (ZW.1.2.1 : Set X.left) \ (ZW.1.1.1 : Set X.left),
      ∃! x : StagePoints k X p ZW, y ∈ closure ({x.1} : Set X.left))
    (r : (D).obj ZW) : ∃ a : ↥(∐ (G)),
      Sigma.desc (pointSupportToConiveauWindow k X K n) a = colimit.ι (D) ZW r := by
  let I := StagePoints k X p ZW
  let : Finite I := (Closeds.finite_coheight_eq ZW.1.2.1 ZW.1.2.2).to_subtype
  let : Fintype I := Fintype.ofFinite I
  refine (Closeds.exists_disjoint_pointClosure_openCover ZW.2 ZW.1.1.2 hgood).elim fun V h ↦ ?_
  exact (stage_is_sum_of_point_classes k X K n p ZW V h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2 r).elim fun s hs ↦
    stage_sum_maps_to_point_sum k X K n p ZW s r hs

/-- The canonical sum of the point inclusions into a coniveau window. -/
def coniveauWindowPointSumMap :
    (∐ (G)) ⟶ coniveauRelativeSupportCohomology k X K n p (p + 1) :=
  Sigma.desc (pointSupportToConiveauWindow k X K n)

private theorem coniveauWindowPointSumMap_injective :
    Function.Injective (coniveauWindowPointSumMap k X K n p) := by
  classical
  let f := coniveauWindowPointSumMap k X K n p
  have hπ (i : ConiveauPoints k X p) : f ≫ coniveauWindowPointProjection k X K n i =
      Sigma.π (G) i := by
    apply Sigma.hom_ext
    intro j
    change Sigma.ι (G) j ≫ f ≫ coniveauWindowPointProjection k X K n i = _
    have hι : Sigma.ι (G) j ≫ f = pointSupportToConiveauWindow k X K n j :=
      Sigma.ι_comp_desc _ _
    rw [← Category.assoc, hι]
    by_cases h : j = i
    · subst j
      rw [pointSupportToConiveauWindow_projection_self, Sigma.ι_π_eq_id]
    · rw [pointSupportToConiveauWindow_projection_of_ne k X K n h, Sigma.ι_π_of_ne _ h]
  intro a b hab
  apply abelianCoproduct_ext (G)
  intro i
  have he (z : ↥(∐ (G))) : Sigma.π (G) i z = coniveauWindowPointProjection k X K n i (f z) :=
    (ConcreteCategory.congr_hom (hπ i) z).symm
  exact (he a).trans ((congrArg (coniveauWindowPointProjection k X K n i) hab).trans (he b).symm)

private theorem coniveauWindowPointSumMap_surjective :
    Function.Surjective (coniveauWindowPointSumMap k X K n p) := by
  let : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{w'}) :=
    preservesFilteredColimitsOfSize_of_univLE.{w',w',u,u} _
  intro s
  obtain ⟨ZW, r, hr⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat.{w'}) (colimit.isColimit (D))) s
  obtain ⟨Z', hZ', hZW', hZ'codim, hgood⟩ := Closeds.exists_enlarge_for_disjoint_pointClosures
    ZW.2 ZW.1.1.2 ZW.1.2.2
  let ZW' : Pairs := ⟨(⟨Z', hZ'codim⟩, ZW.1.2), hZW'⟩
  let j : ZW ⟶ ZW' := homOfLE ⟨hZ', le_rfl⟩
  obtain ⟨a, ha⟩ := stage_generates k X K n p ZW' hgood ((D).map j r)
  refine ⟨a, ha.trans ?_⟩
  exact (ConcreteCategory.congr_hom (colimit.w (D) j) r).trans hr

/-- The original window at two consecutive codimensions is the direct sum of the point groups. -/
@[no_expose]
def coniveauWindowPointSumIso :
    (∐ (G)) ≅ coniveauRelativeSupportCohomology k X K n p (p + 1) :=
  let f := coniveauWindowPointSumMap k X K n p
  letI : Mono f := (AddCommGrpCat.mono_iff_injective f).mpr
    (coniveauWindowPointSumMap_injective k X K n p)
  letI : Epi f := (AddCommGrpCat.epi_iff_surjective f).mpr
    (coniveauWindowPointSumMap_surjective k X K n p)
  letI : IsIso f := isIso_of_mono_of_epi f
  asIso f

variable {p}

/-- The comparison on each point is the canonical point inclusion. -/
@[reassoc (attr := simp)]
theorem ι_coniveauWindowPointSumIso (x : ConiveauPoints k X p) :
    Sigma.ι (G) x ≫ (coniveauWindowPointSumIso k X K n p).hom =
      pointSupportToConiveauWindow k X K n x :=
  Sigma.ι_comp_desc _ _

/-- The inverse to the sum of point inclusions has exactly the original point projections. -/
@[reassoc]
theorem coniveauWindowPointSumIso_inv_π (x : ConiveauPoints k X p) :
    (coniveauWindowPointSumIso k X K n p).inv ≫ Sigma.π (G) x =
      coniveauWindowPointProjection k X K n x := by
  apply (cancel_epi (coniveauWindowPointSumIso k X K n p).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply Sigma.hom_ext
  intro y
  rw [ι_coniveauWindowPointSumIso_assoc]
  classical
  by_cases h : y = x
  · subst y
    rw [Sigma.ι_π_eq_id, pointSupportToConiveauWindow_projection_self]
  · rw [Sigma.ι_π_of_ne _ h, pointSupportToConiveauWindow_projection_of_ne k X K n h]

/-- Maps to a coniveau window are determined by their point projections. -/
theorem coniveauWindow_hom_ext {A : AddCommGrpCat.{w'}}
    (f g : A ⟶ coniveauRelativeSupportCohomology k X K n p (p + 1))
    (h : ∀ x : ConiveauPoints k X p, f ≫ coniveauWindowPointProjection k X K n x =
      g ≫ coniveauWindowPointProjection k X K n x) : f = g := by
  let e := coniveauWindowPointSumIso k X K n p
  apply (cancel_mono e.inv).mp
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  change e.inv (f a) = e.inv (g a)
  apply abelianCoproduct_ext (G)
  intro x
  have he (z : coniveauRelativeSupportCohomology k X K n p (p + 1)) :
      Sigma.π (G) x (e.inv z) = coniveauWindowPointProjection k X K n x z :=
    ConcreteCategory.congr_hom (coniveauWindowPointSumIso_inv_π k X K n x) z
  exact (he (f a)).trans ((ConcreteCategory.congr_hom (h x) a).trans (he (g a)).symm)

end AlgebraicGeometry.MotivicHomotopy

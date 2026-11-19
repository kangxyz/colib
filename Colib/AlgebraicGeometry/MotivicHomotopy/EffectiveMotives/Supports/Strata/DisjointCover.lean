/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Basic
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata.OpenPairs.Maps
public import Colib.AlgebraicGeometry.Sites.Smooth.Zariski.Opens
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Splitting the original relative motives on opens disjoint over the support -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S(" field ")" => Spec (CommRingCat.of field)
local notation "Sm(" field ")" => SmoothSite S(field)
set_option hygiene false in
set_option quotPrecheck false in
local notation "NST(" field ")" => SheafWithTransfers.{u + 1} field

variable (X : Sm(k))

/-- Use the original abelian category of transfer sheaves for disjoint-support excision. -/
local instance disjointCoverAbelianSheafWithTransfers : Abelian NST(k) :=
  SheafWithTransfers.abelian k

private abbrev transferSectionsOnOpens (F : NST(k)) :
    TopCat.Sheaf AddCommGrpCat.{u + 1} X.left.carrier :=
  (SmoothSite.restrictZariskiToOpens X _).obj
    ((SmoothSite.nisnevichToZariskiSheaf S(k) _).obj ((toSheaf k).obj F))

private abbrev transferOpenSectionsEquiv (F : NST(k)) (U : X.left.Opens) :
    ((smoothTransferRepresentable k).obj ((SmoothSite.opensFunctor X).obj U) ⟶ F) ≃+
      (transferSectionsOnOpens k X F).obj.obj (op U) :=
  transferSectionsEquiv k (Cor.mk ((SmoothSite.opensFunctor X).obj U)) F

private theorem transferOpenSectionsEquiv_naturality (F : NST(k)) {U V : X.left.Opens}
    (h : U ≤ V)
    (z : (smoothTransferRepresentable k).obj ((SmoothSite.opensFunctor X).obj V) ⟶ F) :
    (transferSectionsOnOpens k X F).obj.map (homOfLE h).op
        (transferOpenSectionsEquiv k X F V z) =
      transferOpenSectionsEquiv k X F U
        ((smoothTransferRepresentable k).map (relativeOpenInclusion k X h) ≫ z) :=
  (transferSectionsEquiv_naturality_left k F ((Cor.graphFunctor k).map
    (relativeOpenInclusion k X h)) z).symm

private theorem existsUnique_gluing_over_base {T : TopCat.{u}} {I : Type u}
    (F : TopCat.Sheaf AddCommGrpCat.{u + 1} T) {B U : Opens T} (hb : B ≤ U)
    (V : I → Opens T) (hv : ∀ i, V i ≤ U) (hB : ∀ i, B ≤ V i)
    (hcover : U ≤ B ⊔ iSup V) (hinter : ∀ i j, i ≠ j → V i ⊓ V j ≤ B)
    (s : ∀ i, F.obj.obj (op (V i))) (hs : ∀ i, F.obj.map (homOfLE (hB i)).op (s i) = 0) :
    ∃! t : F.obj.obj (op U), F.obj.map (homOfLE hb).op t = 0 ∧
      ∀ i, F.obj.map (homOfLE (hv i)).op t = s i := by
  classical
  let W : Option I → Opens T := fun i ↦ i.elim B V
  let hW : ∀ i, W i ≤ U := fun i ↦ i.recOn hb hv
  let hBW : ∀ i, B ≤ W i := fun i ↦ i.recOn le_rfl hB
  let t : ∀ i, F.obj.obj (op (W i)) := fun i ↦ i.recOn 0 s
  have hBzero (i : Option I) : F.obj.map (homOfLE (hBW i)).op (t i) = 0 := by
    cases i with
    | none => exact map_zero _
    | some i => exact hs i
  have hcov : U ≤ iSup W := hcover.trans (sup_le
    (le_iSup W none) (iSup_le (fun i ↦ le_iSup W (some i))))
  have hcompat : TopCat.Presheaf.IsCompatible F.obj W t := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact congrArg (fun f : W i ⊓ W i ⟶ W i ↦ F.obj.map f.op (t i))
        (Subsingleton.elim _ _)
    have hle : W i ⊓ W j ≤ B := by
      cases i with
      | none => exact inf_le_left
      | some i =>
        cases j with
        | none => exact inf_le_right
        | some j => exact hinter i j (fun h ↦ hij (congrArg some h))
    have hzero (q : Option I) (a : W i ⊓ W j ⟶ W q)
        (he : a = homOfLE (hle.trans (hBW q))) : F.obj.map a.op (t q) = 0 := by
      rw [he, show homOfLE (hle.trans (hBW q)) = homOfLE hle ≫ homOfLE (hBW q) from
        Subsingleton.elim _ _, op_comp, Functor.map_comp_apply, hBzero, map_zero]
    exact (hzero i _ (Subsingleton.elim _ _)).trans (hzero j _ (Subsingleton.elim _ _)).symm
  obtain ⟨z, hz, huniq⟩ := F.existsUnique_gluing' W U (fun i ↦ homOfLE (hW i)) hcov t hcompat
  refine ⟨z, ⟨hz none, fun i ↦ hz (some i)⟩, fun y hy ↦ huniq y ?_⟩
  intro i
  cases i with
  | none => exact hy.1
  | some i => exact hy.2 i

variable {B U : X.left.Opens} (h : B ≤ U) {I : Type u}
  (V : I → X.left.Opens) (hb : ∀ i, B ≤ V i) (hu : ∀ i, V i ≤ U)

/-- The cofan whose maps are induced by the disjoint opens' inclusions of original pairs. -/
abbrev relativeOpenCofan {C : Type*} [Category* C] (P : Arrow Sm(k) ⥤ C) :
    Cofan (fun i ↦ P.obj (relativeOpenPair k X (hb i))) :=
  Cofan.mk (P.obj (relativeOpenPair k X h))
    (fun i ↦ P.map (relativeOpenPairMap k X (hb i) h le_rfl (hu i)))

private def isColimit_relativeOpenCofan_of_sections {C : Type*} [Category* C]
    [Preadditive C] [HasCokernels C] (R : Sm(k) ⥤ C) (P : Arrow Sm(k) ⥤ C)
    (hP : P = R.mapArrow ⋙ coker C)
    (sectionSheaf : C → TopCat.Sheaf AddCommGrpCat.{u + 1} X.left.carrier)
    (sectionEquiv : ∀ (F : C) (T : X.left.Opens),
      (R.obj ((SmoothSite.opensFunctor X).obj T) ⟶ F) ≃+ (sectionSheaf F).obj.obj (op T))
    (sectionEquiv_naturality : ∀ (F : C) {T W : X.left.Opens} (j : T ≤ W)
      (a : R.obj ((SmoothSite.opensFunctor X).obj W) ⟶ F),
      (sectionSheaf F).obj.map (homOfLE j).op (sectionEquiv F W a) =
        sectionEquiv F T (R.map (relativeOpenInclusion k X j) ≫ a))
    (hcover : U ≤ B ⊔ iSup V) (hinter : ∀ i j, i ≠ j → V i ⊓ V j ≤ B) :
    IsColimit (relativeOpenCofan k X h V hb hu P) := by
  subst P
  let P := R.mapArrow ⋙ coker C
  classical
  have hproj (i : I) :
      cokernel.π ((R).map (relativeOpenInclusion k X (hb i))) ≫
          (relativeOpenCofan k X h V hb hu P).inj i =
        (R).map (relativeOpenInclusion k X (hu i)) ≫
          cokernel.π ((R).map (relativeOpenInclusion k X h)) :=
    ((Functor.whiskerLeft R.mapArrow (coker.π C)).naturality
      (relativeOpenPairMap k X (hb i) h le_rfl (hu i))).symm
  have hExist (c : Cofan (fun i ↦ (P).obj (relativeOpenPair k X (hb i)))) :
      ∃! l : (P).obj (relativeOpenPair k X h) ⟶ c.pt,
        ∀ i, (relativeOpenCofan k X h V hb hu P).inj i ≫ l = c.inj i := by
    let F := sectionSheaf c.pt
    let e := sectionEquiv c.pt
    let s (i : I) := e (V i)
      (cokernel.π ((R).map (relativeOpenInclusion k X (hb i))) ≫ c.inj i)
    have hs (i : I) : F.obj.map (homOfLE (hb i)).op (s i) = 0 := by
      rw [sectionEquiv_naturality, ← Category.assoc, cokernel.condition, zero_comp,
        map_zero]
    obtain ⟨t, ht, hut⟩ := existsUnique_gluing_over_base F h V hu hb hcover hinter s hs
    let l := (e U).symm t
    have hl : (R).map (relativeOpenInclusion k X h) ≫ l = 0 := by
      apply (e B).injective
      rw [← sectionEquiv_naturality, AddEquiv.apply_symm_apply, ht.1, map_zero]
    let m := cokernel.desc ((R).map (relativeOpenInclusion k X h)) l hl
    have hm (i : I) : (relativeOpenCofan k X h V hb hu P).inj i ≫ m = c.inj i := by
      apply (cancel_epi (cokernel.π ((R).map (relativeOpenInclusion k X (hb i))))).mp
      rw [← Category.assoc, hproj, Category.assoc, cokernel.π_desc]
      apply (e (V i)).injective
      rw [← sectionEquiv_naturality, AddEquiv.apply_symm_apply]
      exact ht.2 i
    refine ⟨m, hm, fun n hn ↦ ?_⟩
    apply (cancel_epi (cokernel.π ((R).map (relativeOpenInclusion k X h)))).mp
    rw [cokernel.π_desc]
    apply (e U).injective
    rw [AddEquiv.apply_symm_apply]
    apply hut
    refine ⟨?_, fun i ↦ ?_⟩
    · rw [sectionEquiv_naturality, ← Category.assoc, cokernel.condition,
        zero_comp, map_zero]
    · rw [sectionEquiv_naturality, ← Category.assoc, ← hproj,
        Category.assoc, hn i]
  choose m hm huniq using hExist
  exact Cofan.IsColimit.mk _ m hm huniq

/-- The canonical inclusions among the actual transfer quotients of the indicated open pairs. -/
abbrev transferRelativeOpenCofan :=
  relativeOpenCofan k X h V hb hu (transferPairCokernelFunctor k)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- If the covering opens intersect only on the common complementary open, the relative
transfer quotient is their coproduct. Each inclusion is the original map of pairs. -/
@[no_expose]
def transferRelativeOpenCofanIsColimit (hcover : U ≤ B ⊔ iSup V)
    (hinter : ∀ i j, i ≠ j → V i ⊓ V j ≤ B) :
    IsColimit (transferRelativeOpenCofan k X h V hb hu) := by
  let R : Sm(k) ⥤ NST(k) := smoothTransferRepresentable k
  let P : Arrow Sm(k) ⥤ NST(k) := transferPairCokernelFunctor k
  have hP : P = R.mapArrow ⋙ coker NST(k) := rfl
  exact isColimit_relativeOpenCofan_of_sections k X h V hb hu R P hP
    (transferSectionsOnOpens k X) (transferOpenSectionsEquiv k X)
    (transferOpenSectionsEquiv_naturality k X) hcover hinter

private def isColimit_relativeOpenCofan_of_comp {C D : Type*} [Category* C] [Category* D]
    (P : Arrow Sm(k) ⥤ C) (L : C ⥤ D) (Q : Arrow Sm(k) ⥤ D)
    (hQ : Q = P ⋙ L) [PreservesColimitsOfShape (Discrete I) L]
    (hc : IsColimit (relativeOpenCofan k X h V hb hu P)) :
    IsColimit (relativeOpenCofan k X h V hb hu Q) := by
  subst Q
  let c := relativeOpenCofan k X h V hb hu P
  exact (Cofan.isColimitMapCoconeEquiv L _ c) (isColimitOfPreserves L hc)

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S(k)) AddCommGrpCat.{u + 1})]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The relative effective motive splits over a finite open cover with common punctured part. -/
@[no_expose]
def effectiveRelativeOpenCofanIsColimit [Finite I] (hcover : U ≤ B ⊔ iSup V)
    (hinter : ∀ i j, i ≠ j → V i ⊓ V j ≤ B) :
    IsColimit (relativeOpenCofan k X h V hb hu (effectivePairMotiveFunctor k)) := by
  let P : Arrow Sm(k) ⥤ NST(k) := transferPairCokernelFunctor k
  let L : NST(k) ⥤ EffectiveMotivesMinus k := effectiveTransferSheaf k
  let Q : Arrow Sm(k) ⥤ EffectiveMotivesMinus k := effectivePairMotiveFunctor k
  have hQ : Q = P ⋙ L := rfl
  have hc : IsColimit (relativeOpenCofan k X h V hb hu P) :=
    transferRelativeOpenCofanIsColimit k X h V hb hu hcover hinter
  exact isColimit_relativeOpenCofan_of_comp k X h V hb hu P L Q hQ hc

end AlgebraicGeometry.MotivicHomotopy

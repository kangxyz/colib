/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata.Restriction
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.CousinSheaves
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.Tower

/-! # The relative window presheaf is a point-sum sheaf -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.Gersten

open MotivicHomotopy SheafWithTransfers.Gersten

attribute [local instance] specializationOrder

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [UnivLE.{u, w'}]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable (X : Sm(k)) (K : EffectiveMotivesMinus k) (p : ℕ) (n : ℤ)

local notation "O" => SmoothSite.opensFunctor X
set_option quotPrecheck false in
local notation "A" => fun x : ConiveauPoints k X p ↦ pointSupportCohomology k X K n x.1
set_option quotPrecheck false in
local notation "Point" => fun x : ConiveauPoints k X p ↦ x.1

/-- The Cousin term associated with the degree `n` window at codimension `p`. -/
abbrev coniveauCousinPointSheaf :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{w'} :=
  cousinPointSheaf X.left.carrier (Point) (A)

private abbrev PointsInOpen (U : X.left.Opens) := {x : ConiveauPoints k X p // x.1 ∈ U}

private def pointInOpen (U : X.left.Opens) (i : PointsInOpen k X p U) :
    ConiveauPoints k ((O).obj U) p := by
  let f := SmoothSite.openInclusion X U
  let x : ((O).obj U).left := ⟨i.1.1, i.2⟩
  exact ⟨x, (Topology.IsOpenEmbedding.coheight_eq (x := x) f.left f.left.isOpenEmbedding).symm.trans
    i.1.2⟩

private def pointInOpenEquiv (U : X.left.Opens) :
    PointsInOpen k X p U ≃ ConiveauPoints k ((O).obj U) p where
  toFun := pointInOpen k X p U
  invFun x := ⟨coniveauPointImage k (SmoothSite.openInclusion X U) x, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def pointTermsIso (U : X.left.Opens) :
    (∐ fun i : PointsInOpen k X p U ↦ (A) i.1) ≅
      ∐ fun i : ConiveauPoints k ((O).obj U) p ↦ pointSupportCohomology k ((O).obj U) K n i.1 := by
  let e := pointInOpenEquiv k X p U
  let f := SmoothSite.openInclusion X U
  let B₀ (i : PointsInOpen k X p U) := (A) i.1
  let B₁ (i : ConiveauPoints k ((O).obj U) p) := pointSupportCohomology k ((O).obj U) K n i.1
  let h (i : ConiveauPoints k ((O).obj U) p) : B₀ (e.symm i) ≅ B₁ i :=
    pointSupportOpenRestrictionIso k f K n i.1
  let l (i : PointsInOpen k X p U) : B₀ i ≅ B₁ (e i) := h (e i)
  exact Sigma.whiskerEquiv e (fun i ↦ (l i).symm)

private def coniveauWindowCousinSectionsIso (U : X.left.Opens) :
    (coniveauCousinPointSheaf k X K p n).obj.obj (op U) ≅
      (coniveauWindowPresheaf k X K p n).obj (op U) :=
  (cousinPointSectionsIso X.left.carrier (Point) (A) U (NoetherianSpace.isCompact _)).symm ≪≫
    pointTermsIso k X K p n U ≪≫ coniveauWindowPointSumIso k ((O).obj U) K n p

@[reassoc]
private theorem cousinPointSectionι_windowSectionsIso (U : X.left.Opens)
    (i : PointsInOpen k X p U) :
    cousinPointSectionι X.left.carrier (Point) (A) U i ≫
      (coniveauWindowCousinSectionsIso k X K p n U).hom =
        pointSupportToConiveauWindow k X K n i.1 ≫
          coniveauRelativeSupportOpenRestriction k X K n p (p + 1) U := by
  let e := cousinPointSectionsIso X.left.carrier (Point) (A) U (NoetherianSpace.isCompact _)
  rw [← cousinPointSectionsIso_ι X.left.carrier (Point) (A) U (NoetherianSpace.isCompact _) i,
    coniveauWindowCousinSectionsIso, Iso.trans_hom, Category.assoc]
  change Sigma.ι _ i ≫ e.hom ≫ e.inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  simp only [pointTermsIso, Sigma.whiskerEquiv_hom, Sigma.map', Iso.symm_inv, Iso.trans_hom,
    Sigma.ι_comp_desc_assoc, Category.assoc, ι_coniveauWindowPointSumIso]
  rw [coniveauRelativeSupportOpenRestriction_eq_restrict]
  exact (pointSupportToConiveauWindow_openRestriction k (SmoothSite.openInclusion X U) K n
    (pointInOpen k X p U i)).symm

private theorem coniveauRelativeSupportOpenRestriction_comp_openMap {U V : X.left.Opens}
    (f : V ⟶ U) :
    coniveauRelativeSupportOpenRestriction k X K n p (p + 1) U ≫
        coniveauRelativeSupportOpenMap k X K n p (p + 1) f =
      coniveauRelativeSupportOpenRestriction k X K n p (p + 1) V := by
  rw [coniveauRelativeSupportOpenRestriction_eq_restrict,
    coniveauRelativeSupportOpenMap_eq_restrict,
    coniveauRelativeSupportOpenRestriction_eq_restrict, ← coniveauRelativeSupportRestrict_comp]
  apply coniveauRelativeSupportRestrict_congr
  exact MorphismProperty.Over.Hom.ext (X.left.homOfLE_ι f.le)

/-- The point-sum description of each coniveau window is natural on actual ambient opens. -/
@[no_expose]
def coniveauWindowCousinPresheafIso : (coniveauCousinPointSheaf k X K p n).obj ≅
    coniveauWindowPresheaf k X K p n :=
  NatIso.ofComponents (fun U ↦ coniveauWindowCousinSectionsIso k X K p n U.unop) (by
    intro U V f
    apply Cofan.IsColimit.hom_ext
      (cousinPointSectionsIsColimit X.left.carrier (Point) (A) U.unop
        (NoetherianSpace.isCompact _))
    intro i
    change cousinPointSectionι X.left.carrier (Point) (A) U.unop i ≫
      (coniveauCousinPointSheaf k X K p n).obj.map f ≫
      (coniveauWindowCousinSectionsIso k X K p n V.unop).hom =
        cousinPointSectionι X.left.carrier (Point) (A) U.unop i ≫
        (coniveauWindowCousinSectionsIso k X K p n U.unop).hom ≫
        coniveauRelativeSupportOpenMap k X K n p (p + 1) f.unop
    rw [cousinPointSectionι_windowSectionsIso_assoc,
      coniveauRelativeSupportOpenRestriction_comp_openMap]
    by_cases hi : i.1.1 ∈ V.unop
    · exact (cousinPointSectionι_restrict_assoc X.left.carrier (Point) (A) f.unop i.1 hi _).trans
        (cousinPointSectionι_windowSectionsIso k X K p n V.unop ⟨i.1, hi⟩)
    · have hzero : cousinPointSectionι X.left.carrier (Point) (A) U.unop i ≫
          (coniveauCousinPointSheaf k X K p n).obj.map f = 0 :=
        cousinPointSectionι_restrict_eq_zero X.left.carrier (Point) (A) f.unop i hi
      rw [reassoc_of% hzero, zero_comp, coniveauRelativeSupportOpenRestriction_eq_restrict]
      symm
      apply pointSupportToConiveauWindow_openRestriction_eq_zero
      rwa [show Set.range (SmoothSite.openInclusion X V.unop).left = (V.unop : Set X.left) from
        Scheme.Opens.range_ι V.unop])

end AlgebraicGeometry.Gersten

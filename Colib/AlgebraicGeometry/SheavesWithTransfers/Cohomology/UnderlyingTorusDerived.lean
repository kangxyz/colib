/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.UnderlyingPresheafDerived
public import Colib.CategoryTheory.Sites.Simplicial.ParameterCoproduct
import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Continuity
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategorySquare

/-!
# Derived torus sections on the underlying ordinary presheaves

Graph restriction of signed torus products is the original product of
smooth schemes. After taking ordinary derived presheaves this gives
the exact parameter reindexing used by the pointed cylinder adjunction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u w₁ w₂ w₃ w₄ w₅

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers
open CategoryTheory.PointedSimplicialPresheaf.ParameterCoproduct

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "J" => SmoothSite.nisnevichTopology S
local notation "A" => LargeAb k
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "V" => toPresheaf k
local notation "T" => withParameterFunctor G
local notation "P" => reindex G A

/-- The exact ordinary presheaf comparison for the original torus product. -/
@[no_expose]
def torusGraphRestrictionIso :
    (T : LargePresheaves k ⥤ LargePresheaves k) ⋙ V ≅ V ⋙ P := by
  let W : LargePresheaves k ⥤ (SmoothSite S)ᵒᵖ ⥤ A := V
  let d := NatIso.op (SmoothSite.Contraction.categoricalParameterProductIso G)
  let e (M : LargePresheaves k) := withParameterUnderlyingIso M G ≪≫
    Functor.isoWhiskerRight d (W.obj M)
  refine NatIso.ofComponents e ?_
  intro M N f
  apply NatTrans.ext
  funext X
  let i := (SmoothSite.categoricalProductIso X.unop G).hom
  let a := (W.map f).app (op (SmoothSite.product X.unop G))
  let b := (W.map f).app (op (X.unop ⨯ G))
  have hn : (W.obj M).map i.op ≫ b = a ≫ (W.obj N).map i.op :=
    (W.map f).naturality i.op
  change a ≫ (𝟙 _ ≫ (W.obj N).map i.op) = (𝟙 _ ≫ (W.obj M).map i.op) ≫ b
  exact (congrArg (a ≫ ·) (Category.id_comp _)).trans
    (hn.symm.trans (congrArg (· ≫ b) (Category.id_comp _).symm))

/-- At each smooth object the comparison pulls back by the native product isomorphism. -/
theorem torusGraphRestrictionIso_hom_app_app
    (M : LargePresheaves k) (X : SmoothSite S) :
    ((torusGraphRestrictionIso k).hom.app M).app (op X) =
      ((toPresheaf k).obj M).map (SmoothSite.categoricalProductIso X G).hom.op := by
  unfold torusGraphRestrictionIso
  change 𝟙 _ ≫ ((toPresheaf k).obj M).map (SmoothSite.categoricalProductIso X G).hom.op = _
  exact Category.id_comp _

section Derived

variable [HasDerivedCategory.{w₁} (LargePresheaves k)]
  [HasDerivedCategory.{w₂} (LargeSheaves k)]
  [HasDerivedCategory.{w₃}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

instance ordinaryTorusReindexAdditive : (P).Additive where
  map_add := rfl

/-- Ordinary derived presheaves of the actual transfer torus sections
are obtained by exact precomposition with the original torus product. -/
@[no_expose]
def torusSectionsDerivedOrdinaryPresheafIso :
    torusSectionsDerivedFunctor k ⋙ (toSheaf k).mapDerivedCategory ⋙
        ordinaryPresheafDerivedFunctor k ≅
      ((toSheaf k).mapDerivedCategory ⋙ ordinaryPresheafDerivedFunctor k) ⋙
        (P).mapDerivedCategory := by
  let U := forgetDerivedFunctor k
  let B := torusSectionsDerivedFunctor k
  let e := forgetDerivedOrdinaryPresheafIso k
  let v := (toPresheaf.{u + 1} k).mapDerivedCategory
  let t := (T : LargePresheaves k ⥤ LargePresheaves k).mapDerivedCategory
  let p := (P).mapDerivedCategory
  let d : t ⋙ v ≅ v ⋙ p := Functor.mapDerivedCategorySquareIso (torusGraphRestrictionIso k)
  exact Functor.isoWhiskerLeft B e.symm ≪≫
    (Functor.associator B U v).symm ≪≫
    Functor.isoWhiskerRight (torusSectionsDerivedForgetIso k) v ≪≫
    Functor.associator U t v ≪≫ Functor.isoWhiskerLeft U d ≪≫
    (Functor.associator U v p).symm ≪≫ Functor.isoWhiskerRight e p

/-- The comparison uses the original derived forget and graph restriction
isomorphisms at each coefficient. -/
theorem torusSectionsDerivedOrdinaryPresheafIso_hom_app
    (K : DerivedCategory (LargeSheaves k)) :
    let U := forgetDerivedFunctor k
    let B := torusSectionsDerivedFunctor k
    let e := forgetDerivedOrdinaryPresheafIso k
    let v := (toPresheaf.{u + 1} k).mapDerivedCategory
    let p := (P).mapDerivedCategory
    let d := Functor.mapDerivedCategorySquareIso (torusGraphRestrictionIso k)
    (torusSectionsDerivedOrdinaryPresheafIso k).hom.app K =
      e.inv.app (B.obj K) ≫ v.map ((torusSectionsDerivedForgetIso k).hom.app K) ≫
        d.hom.app (U.obj K) ≫ p.map (e.hom.app K) := by
  intro U B e v p d
  unfold torusSectionsDerivedOrdinaryPresheafIso
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  rfl

end Derived

end AlgebraicGeometry.SheafWithTransfers

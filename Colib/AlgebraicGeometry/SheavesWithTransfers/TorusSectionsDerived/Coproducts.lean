/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.EffectiveHomology
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedFunctor
import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsCoproducts
import Mathlib.CategoryTheory.MorphismProperty.Retract
import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums
import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyBaseCase
import StacksFrontier.CategoryTheory.Triangulated.CoproductComparison

/-!
# Direct sums of effective derived torus sections

Exact direct sums of transfer sheaves commute with cohomology.
The natural cohomology comparison reduces the original derived
direct-sum map to ordinary torus sections. The reduced comparison
is its retract under the original unit splitting.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

variable {I : Type (u + 1)} (K : I → DerivedCategory (SheafWithTransfers.{u + 1} k))
  [HasCoproductsOfShape I (DerivedCategory (SheafWithTransfers.{u + 1} k))]

/-- The canonical direct-sum comparison for total derived torus sections
is an isomorphism on a family with A¹-invariant cohomology and whose sum
has A¹-invariant cohomology. -/
theorem isIso_sigmaComparison_torusSectionsDerived
    [PerfectField k] [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (hK : ∀ j, a1InvariantCohomology k (K j))
    (hSum : a1InvariantCohomology k (∐ K)) :
    IsIso (sigmaComparison (torusSectionsDerivedFunctor k) K) := by
  let A := SheafWithTransfers.{u + 1} k
  let R := torusSectionsDerivedFunctor k
  let B : A ⥤ A := torusSectionsFunctor k
  let : PreservesColimitsOfShape (Discrete I) B := torusSectionsFunctor_preservesCoproducts k I
  apply (DerivedCategory.isIso_iff A (sigmaComparison R K)).2
  intro n
  let H := DerivedCategory.homologyFunctor A n
  let F := R ⋙ H
  let G := H ⋙ B
  let e := torusSectionsDerivedHomologyNatIso k n
  let Z : (a1InvariantCohomology k).FullSubcategory := ⟨∐ K, hSum⟩
  let X (j : I) : (a1InvariantCohomology k).FullSubcategory := ⟨K j, hK j⟩
  let eSum : F.obj (∐ K) ≅ G.obj (∐ K) := e.app Z
  let eK (j : I) : F.obj (K j) ≅ G.obj (K j) := e.app (X j)
  let : PreservesColimitsOfShape (Discrete I) H :=
    Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor A n
  let a : Discrete.functor (fun j => F.obj (K j)) ≅
      Discrete.functor (fun j => G.obj (K j)) :=
    Discrete.natIso (fun j => eK j.as)
  let d := HasColimit.isoOfNatIso a
  have h : sigmaComparison F K ≫ eSum.hom = d.hom ≫ sigmaComparison G K := by
    refine Sigma.hom_ext _ _ (fun j => ?_)
    have hn : F.map (Sigma.ι K j) ≫ eSum.hom = (eK j).hom ≫ G.map (Sigma.ι K j) :=
      e.hom.naturality (ObjectProperty.homMk (X := X j) (Y := Z) (Sigma.ι K j))
    have hd : Sigma.ι (fun j => F.obj (K j)) j ≫ d.hom =
        (eK j).hom ≫ Sigma.ι (fun j => G.obj (K j)) j :=
      HasColimit.ι_isoOfNatIso_hom a (Discrete.mk j)
    calc
      _ = F.map (Sigma.ι K j) ≫ eSum.hom := ι_comp_sigmaComparison_assoc F K j _
      _ = (eK j).hom ≫ G.map (Sigma.ι K j) := hn
      _ = (eK j).hom ≫ (Sigma.ι (fun j => G.obj (K j)) j ≫ sigmaComparison G K) :=
        congrArg ((eK j).hom ≫ ·) (ι_comp_sigmaComparison G K j).symm
      _ = ((eK j).hom ≫ Sigma.ι (fun j => G.obj (K j)) j) ≫ sigmaComparison G K :=
        (Category.assoc _ _ _).symm
      _ = _ := (congrArg (· ≫ sigmaComparison G K) hd.symm).trans (Category.assoc _ _ _)
  let hs : IsIso (sigmaComparison G K) :=
    isIso_sigmaComparison_of_preservesColimit G K inferInstance
  let : IsIso (sigmaComparison F K ≫ eSum.hom) :=
    h.symm ▸ IsIso.comp_isIso' d.isIso_hom hs
  have hF : IsIso (sigmaComparison F K) := IsIso.of_isIso_comp_right _ eSum.hom
  exact isIso_map_sigmaComparison_of_isIso_comp R H K hF
    (isIso_sigmaComparison_of_preservesColimit H (fun j => R.obj (K j)) inferInstance)

/-- Direct sums retain A¹-invariance of the actual transfer cohomology
sheaves. -/
theorem a1InvariantCohomology_sigma
    (hK : ∀ j, a1InvariantCohomology k (K j)) :
    a1InvariantCohomology k (∐ K) := by
  intro n X
  let A := SheafWithTransfers.{u + 1} k
  let H := DerivedCategory.homologyFunctor A n
  let S := Spec (CommRingCat.of k)
  let d := ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject S)).app X).op
  let U : A ⥤ (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    SheafWithTransfers.forget k ⋙ PresheafWithTransfers.toPresheaf k
  let J := Discrete I
  let : PreservesColimitsOfShape J H :=
    Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor A n
  let : PreservesColimitsOfShape J (SheafWithTransfers.forget.{u + 1} k) :=
    forget_preservesCoproducts k I
  let F := H ⋙ U
  let : PreservesColimitsOfShape J F := inferInstance
  let E := CategoryTheory.evaluation (SmoothSite S)ᵒᵖ AddCommGrpCat.{u + 1}
  let L := F ⋙ E.obj (Opposite.op X)
  let R := F ⋙ E.obj (Opposite.op (SmoothSite.Contraction.affineLineCylinder.obj X))
  let e : L ⟶ R := Functor.whiskerLeft F (E.map d)
  change IsIso (e.app (∐ K))
  let D := Discrete.functor K
  let : IsIso (Functor.whiskerLeft D e) :=
    (NatTrans.isIso_iff_isIso_app _).2 (fun j => hK j.as n X)
  have h : colim.map (Functor.whiskerLeft D e) ≫ colimit.post D R =
      colimit.post D L ≫ e.app (∐ K) :=
    Stacks.Cohomology.ColimitsOfCohomology.colim_map_whiskerLeft_comp_colimit_post D e
  let : IsIso (colimit.post D L ≫ e.app (∐ K)) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_left (colimit.post D L) _

/-- The canonical direct-sum comparison for reduced derived torus
sections is an isomorphism on the A¹-invariant cohomology objects. -/
theorem isIso_sigmaComparison_reducedTorusSectionsDerived
    [PerfectField k] [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (hK : ∀ j, a1InvariantCohomology k (K j)) :
    IsIso (sigmaComparison (reducedTorusSectionsDerivedFunctor k) K) := by
  let N := reducedTorusSectionsDerivedFunctor k
  let R := torusSectionsDerivedFunctor k
  let i := reducedTorusSectionsDerivedInclusion k
  let r := reducedTorusSectionsDerivedProjection k
  let p := sigmaComparison N K
  let q := sigmaComparison R K
  let iSum := Limits.Sigma.map (fun j => i.app (K j))
  let rSum := Limits.Sigma.map (fun j => r.app (K j))
  let n (j : I) := Sigma.ι (fun j => N.obj (K j)) j
  let t (j : I) := Sigma.ι (fun j => R.obj (K j)) j
  have hi : iSum ≫ q = p ≫ i.app (∐ K) := by
    refine Limits.Sigma.hom_ext _ _ (fun j => ?_)
    calc
      _ = i.app (K j) ≫ t j ≫ q := Limits.Sigma.ι_map_assoc _ j _
      _ = i.app (K j) ≫ R.map (Sigma.ι K j) :=
        congrArg (i.app (K j) ≫ ·) (ι_comp_sigmaComparison R K j)
      _ = N.map (Sigma.ι K j) ≫ i.app (∐ K) := (i.naturality (Sigma.ι K j)).symm
      _ = _ := (ι_comp_sigmaComparison_assoc N K j _).symm
  have hr : rSum ≫ p = q ≫ r.app (∐ K) := by
    refine Limits.Sigma.hom_ext _ _ (fun j => ?_)
    calc
      _ = r.app (K j) ≫ n j ≫ p := Limits.Sigma.ι_map_assoc _ j _
      _ = r.app (K j) ≫ N.map (Sigma.ι K j) :=
        congrArg (r.app (K j) ≫ ·) (ι_comp_sigmaComparison N K j)
      _ = R.map (Sigma.ι K j) ≫ r.app (∐ K) := (r.naturality (Sigma.ι K j)).symm
      _ = _ := (ι_comp_sigmaComparison_assoc R K j _).symm
  have hsplit : iSum ≫ rSum = 𝟙 _ := by
    refine Limits.Sigma.hom_ext _ _ (fun j => ?_)
    calc
      _ = i.app (K j) ≫ t j ≫ rSum := Limits.Sigma.ι_map_assoc _ j _
      _ = i.app (K j) ≫ r.app (K j) ≫ n j :=
        congrArg (i.app (K j) ≫ ·) (Limits.Sigma.ι_map _ j)
      _ = n j := reducedTorusSectionsDerivedInclusion_projection_assoc k (K j) _
      _ = _ := (Category.comp_id _).symm
  let e : RetractArrow p q :=
    { i := Arrow.homMk' iSum (i.app (∐ K)) hi
      r := Arrow.homMk' rSum (r.app (∐ K)) hr
      retract := Arrow.hom_ext _ _ hsplit
        (reducedTorusSectionsDerivedInclusion_projection k _) }
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _) e
    (isIso_sigmaComparison_torusSectionsDerived k K hK (a1InvariantCohomology_sigma k K hK))

end AlgebraicGeometry.SheafWithTransfers

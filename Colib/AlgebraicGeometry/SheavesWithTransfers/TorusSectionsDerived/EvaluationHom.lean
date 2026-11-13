/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.DerivedCategory.CorepresentedTotalEvaluation
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.Evaluation
public import Colib.CategoryTheory.Sites.Hypercohomology.FiniteWindow

/-!
# The derived Hom of actual torus sections

The represented evaluation comparison identifies the shifted Hom out of
the smooth representable with shifted Hom out of its original torus
product. This comparison carries coefficient maps to shifted postcomposition.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open Stacks.Cohomology.Corepresented

universe w w' u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S

/-- Derived Hom from the actual smooth representable into torus sections
is derived Hom from the actual torus-product representable. -/
def torusSectionsDerivedHomAddEquiv (X : SmoothSite S)
    (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) (p : ℤ) :
    ((DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj (Cor.mk X)) ⟶
      ((torusSectionsDerivedFunctor k).obj K)⟦p⟧) ≃+
    ((DerivedCategory.singleFunctor _ 0).obj
        ((transferRepresentable k).obj (Cor.mk (SmoothSite.product X G))) ⟶ K⟦p⟧) :=
  let XT := SmoothSite.product X G
  let RX := (transferRepresentable k).obj (Cor.mk X)
  let RXT := (transferRepresentable k).obj (Cor.mk XT)
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p
  let E := torusSectionsEvaluationDerivedIso k X
  let eX := totalCorepresentedHomologyAddEquiv (transferEvaluationFunctor k X) RX
    (Iso.refl _) (transferEvaluationDerivedFunctor k X) (transferEvaluationDerivedUnit k X)
    p ((torusSectionsDerivedFunctor k).obj K)
  let eXT := totalCorepresentedHomologyAddEquiv (transferEvaluationFunctor k XT) RXT
    (Iso.refl _) (transferEvaluationDerivedFunctor k XT) (transferEvaluationDerivedUnit k XT) p K
  eX.symm.trans (((H.mapIso (E.app K)).addCommGroupIsoToAddEquiv).trans eXT)

/-- The same equivalence carries the actual derived torus map of a
coefficient morphism to the original shifted coefficient morphism. -/
theorem torusSectionsDerivedHomAddEquiv_naturality (X : SmoothSite S)
    {K L : DerivedCategory (SheafWithTransfers.{u + 1} k)} (f : K ⟶ L) (p : ℤ)
    (a : (DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj (Cor.mk X)) ⟶
      ((torusSectionsDerivedFunctor k).obj K)⟦p⟧) :
    torusSectionsDerivedHomAddEquiv k X L p
        (a ≫ ((torusSectionsDerivedFunctor k).map f)⟦p⟧') =
      torusSectionsDerivedHomAddEquiv k X K p a ≫ f⟦p⟧' := by
  let XT := SmoothSite.product X G
  let RX := (transferRepresentable k).obj (Cor.mk X)
  let RXT := (transferRepresentable k).obj (Cor.mk XT)
  let R := torusSectionsDerivedFunctor k
  let V := transferEvaluationDerivedFunctor k X
  let W := transferEvaluationDerivedFunctor k XT
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p
  let E := torusSectionsEvaluationDerivedIso k X
  let eX := totalCorepresentedHomologyAddEquiv (transferEvaluationFunctor k X) RX
    (Iso.refl _) V (transferEvaluationDerivedUnit k X) p
  let eXT := totalCorepresentedHomologyAddEquiv (transferEvaluationFunctor k XT) RXT
    (Iso.refl _) W (transferEvaluationDerivedUnit k XT) p
  let b := (eX (R.obj K)).symm a
  have hX : (eX (R.obj L)).symm (a ≫ (R.map f)⟦p⟧') = H.map (V.map (R.map f)) b := by
    apply (eX (R.obj L)).injective
    rw [AddEquiv.apply_symm_apply]
    exact (congrArg (· ≫ (R.map f)⟦p⟧') ((eX (R.obj K)).apply_symm_apply a)).symm.trans
      (totalCorepresentedHomologyAddEquiv_naturality (transferEvaluationFunctor k X) RX
        (Iso.refl _) V (transferEvaluationDerivedUnit k X) p (R.map f) b).symm
  have hE : H.map (V.map (R.map f)) ≫ H.map (E.hom.app L) =
      H.map (E.hom.app K) ≫ H.map (W.map f) :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (E.hom.naturality f)).trans (H.map_comp _ _))
  have hE' := ConcreteCategory.congr_hom hE b
  change H.map (E.hom.app L) (H.map (V.map (R.map f)) b) =
    H.map (W.map f) (H.map (E.hom.app K) b) at hE'
  change eXT L (H.map (E.hom.app L) ((eX (R.obj L)).symm (a ≫ (R.map f)⟦p⟧'))) =
    eXT K (H.map (E.hom.app K) b) ≫ f⟦p⟧'
  rw [hX, hE']
  exact totalCorepresentedHomologyAddEquiv_naturality (transferEvaluationFunctor k XT) RXT
    (Iso.refl _) W (transferEvaluationDerivedUnit k XT) p f _

/-- For a smooth representable the actual shifted Hom into the derived
torus functor respects the finite truncation cutoff on the target. -/
theorem bijective_comp_torusSectionsDerived_map_truncGEπ (X : SmoothSite S)
    (K : DerivedCategory (SheafWithTransfers.{u + 1} k))
    (d : ℕ) [HasProjectiveDimensionLE
      ((transferRepresentable k).obj (Cor.mk (SmoothSite.product X G))) d] (p : ℤ) :
    Function.Bijective (fun f :
      (DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj (Cor.mk X)) ⟶
        ((torusSectionsDerivedFunctor k).obj K)⟦p⟧ =>
      f ≫ ((torusSectionsDerivedFunctor k).map
        ((DerivedCategory.TStructure.t.truncGEπ (p - (d : ℤ))).app K))⟦p⟧') := by
  let R := torusSectionsDerivedFunctor k
  let L := (DerivedCategory.TStructure.t.truncGE (p - (d : ℤ))).obj K
  let π : K ⟶ L := (DerivedCategory.TStructure.t.truncGEπ (p - (d : ℤ))).app K
  let X₀ := (DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj (Cor.mk X))
  let Z := (transferRepresentable k).obj (Cor.mk (SmoothSite.product X G))
  let X₁ := (DerivedCategory.singleFunctor _ 0).obj Z
  let e₀ := torusSectionsDerivedHomAddEquiv k X K p
  let e₁ := torusSectionsDerivedHomAddEquiv k X L p
  let f (a : X₀ ⟶ (R.obj K)⟦p⟧) := a ≫ (R.map π)⟦p⟧'
  let g (a : X₁ ⟶ K⟦p⟧) := a ≫ π⟦p⟧'
  have h : e₁ ∘ f = g ∘ e₀ := funext (fun a =>
    torusSectionsDerivedHomAddEquiv_naturality k X π p a)
  change Function.Bijective f
  apply (Function.Bijective.of_comp_iff' e₁.bijective f).mp
  rw [h]
  exact (DerivedCategory.bijective_comp_truncGEπ_of_hasProjectiveDimensionLE Z d K p).comp
    e₀.bijective

end AlgebraicGeometry.SheafWithTransfers

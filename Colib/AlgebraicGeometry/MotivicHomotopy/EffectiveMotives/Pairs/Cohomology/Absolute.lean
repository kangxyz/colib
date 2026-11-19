/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Cohomology.Coefficient
public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.Representability
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.OrdinaryComparison
import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.AffineContraction
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Ordinary Nisnevich cohomology represented by smooth effective motives -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry.Scheme Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Nis" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))
local notation "NST" => LargeSheaves k
local notation "M" => effectiveSmoothMotive k
local notation "J" => effectiveMotivesMinusToDerived k

/-- The actual Nisnevich sheafification on smooth schemes. -/
local instance absoluteHasSheafify : HasSheafify Nis AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1} Nis

/-- Use the original abelian transfer category for the single coefficients. -/
local instance absoluteCohomologyAbelian : Abelian NST := SheafWithTransfers.abelian k

/-- Use the Ext groups of the chosen transfer derived category. -/
local instance absoluteCohomologyHasExt : HasExt.{w'} NST := hasExt_of_hasDerivedCategory NST

/-- The smooth derived comparison with Ext from the original transfer representable. -/
def effectiveSmoothExtEquiv (X : SmoothSite (Spec (.of k))) (F : NST)
    (hF : F.obj.IsA1Invariant) (n : ℕ) :
    ((M).obj X ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) ≃+
      Ext.{w'} ((transferRepresentable k).obj (Cor.mk X)) F n := by
  let K := effectiveHICoefficient k F hF
  let b := ((J).commShiftIso (n : ℤ)).app K
  exact (effectiveMotiveDerivedHomEquiv k (Cor.mk X) (K⟦(n : ℤ)⟧)).trans
    ((AddEquiv.mk' b.homToEquiv (fun x y => Preadditive.add_comp _ _ _ x y b.hom)).trans
      Ext.homAddEquiv.symm)

/-- The Ext class is realized by the original derived transpose and shift isomorphism. -/
theorem effectiveSmoothExtEquiv_hom (X : SmoothSite (Spec (.of k))) (F : NST)
    (hF : F.obj.IsA1Invariant) (n : ℕ)
    (x : (M).obj X ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    (effectiveSmoothExtEquiv k X F hF n x).hom =
      effectiveMotiveDerivedHomEquiv k (Cor.mk X) ((effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) x ≫
        ((J).commShiftIso (n : ℤ)).hom.app (effectiveHICoefficient k F hF) :=
  Ext.homAddEquiv.apply_symm_apply _

set_option maxHeartbeats 600000 in
-- Identify the original Ext source and the shifted target of graph precomposition.
private theorem effectiveSmoothExtEquiv_precomp {Y Z : SmoothSite (Spec (.of k))} (f : Y ⟶ Z)
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (x : (M).obj Z ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectiveSmoothExtEquiv k Y F hF n ((M).map f ≫ x) =
      (Ext.mk₀ ((transferRepresentable k).map ((Cor.graphFunctor k).map f))).comp
        (effectiveSmoothExtEquiv k Z F hF n x) (zero_add n) := by
  apply Ext.ext
  let K := effectiveHICoefficient k F hF
  let g := (Cor.graphFunctor k).map f
  let r := (transferRepresentable k).map g
  let d := (DerivedCategory.singleFunctor NST 0).map r
  let b := ((J).commShiftIso (n : ℤ)).hom.app K
  let y := (effectiveMotive k).map g ≫ x
  let z := effectiveMotiveDerivedHomEquiv k (Cor.mk Z) (K⟦(n : ℤ)⟧) x
  let e := effectiveSmoothExtEquiv k Z F hF n x
  have hY := effectiveSmoothExtEquiv_hom k Y F hF n y
  have hZ := effectiveSmoothExtEquiv_hom k Z F hF n x
  have hGraph := effectiveMotiveDerivedHomEquiv_precomp k g (K := K⟦(n : ℤ)⟧) x
  have hShift := congrArg (· ≫ b) hGraph
  have hAssoc := Category.assoc d z b
  have hCoeff := congrArg (d ≫ ·) hZ.symm
  have hExt := Ext.singleFunctor_map_comp_hom r e
  have h := hY.trans (hShift.trans (hAssoc.trans (hCoeff.trans hExt)))
  exact h

private theorem effectiveSmoothExtEquiv_postcomp (Y : SmoothSite (Spec (.of k))) {F G : NST}
    (hF : F.obj.IsA1Invariant) (hG : G.obj.IsA1Invariant) (f : F ⟶ G) (n : ℕ)
    (x : (M).obj Y ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectiveSmoothExtEquiv k Y G hG n
        (x ≫ (effectiveHICoefficientMap k hF hG f)⟦(n : ℤ)⟧') =
      (effectiveSmoothExtEquiv k Y F hF n x).comp (Ext.mk₀ f) (add_zero n) := by
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀, effectiveSmoothExtEquiv_hom,
    effectiveMotiveDerivedHomEquiv_comp, Category.assoc, Functor.commShiftIso_hom_naturality,
    effectiveHICoefficientMap_toDerived]

/-- The ordinary cohomology of a smooth scheme is represented by its effective motive. -/
def effectiveSmoothCohomologyEquiv (Y : SmoothSite (Spec (.of k))) (F : NST)
    (hF : F.obj.IsA1Invariant) (n : ℕ) :
    ((M).obj Y ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) ≃+
      (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) n).obj (op Y) :=
  (effectiveSmoothExtEquiv k Y F hF n).trans (transferExtEquiv.{w', u + 1, u} k Y F n)

/-- The comparison on smooth motives uses the original graph restriction. -/
theorem effectiveSmoothCohomologyEquiv_precomp {Y Z : SmoothSite (Spec (.of k))} (f : Y ⟶ Z)
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (x : (M).obj Z ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectiveSmoothCohomologyEquiv k Y F hF n ((M).map f ≫ x) =
      (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) n).map f.op
        (effectiveSmoothCohomologyEquiv k Z F hF n x) := by
  simp only [effectiveSmoothCohomologyEquiv, AddEquiv.trans_apply, effectiveSmoothExtEquiv_precomp]
  exact transferExtEquiv_naturality_graph.{w', u + 1, u} k f F n _

/-- The smooth comparison acts by ordinary maps of coefficients. -/
theorem effectiveSmoothCohomologyEquiv_postcomp (Y : SmoothSite (Spec (.of k))) {F G : NST}
    (hF : F.obj.IsA1Invariant) (hG : G.obj.IsA1Invariant) (f : F ⟶ G) (n : ℕ)
    (x : (M).obj Y ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectiveSmoothCohomologyEquiv k Y G hG n
        (x ≫ (effectiveHICoefficientMap k hF hG f)⟦(n : ℤ)⟧') =
      ((cohomologyPresheafFunctor.{u + 1, u + 1} Nis n).map ((toSheaf k).map f)).app
        (op Y) (effectiveSmoothCohomologyEquiv k Y F hF n x) := by
  simp only [effectiveSmoothCohomologyEquiv, AddEquiv.trans_apply, effectiveSmoothExtEquiv_postcomp]
  exact transferExtEquiv_naturality_coeff.{w', u + 1, u} k Y f n _

/-- A degree below zero gives no class on a smooth effective motive. -/
theorem effectiveSmoothCohomology_eq_zero_of_neg (Y : SmoothSite (Spec (.of k)))
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℤ) (hn : n < 0)
    (x : (M).obj Y ⟶ (effectiveHICoefficient k F hF)⟦n⟧) : x = 0 := by
  let eY := effectiveMotiveDerivedHomEquiv k (Cor.mk Y) ((effectiveHICoefficient k F hF)⟦n⟧)
  apply eY.injective
  rw [map_zero]
  exact derivedHom_to_effectiveHICoefficient_shift_eq_zero_of_neg k _ F hF n hn _

end AlgebraicGeometry.MotivicHomotopy

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.DerivedDetection
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.EvaluationHom
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.SingularTruncation
import Colib.AlgebraicGeometry.Sites.Smooth.FiniteKrullDimension

/-!
# Shifted Hom comparison for the original singular torus map

Finite projective dimension at a smooth scheme and its torus product
gives a common truncation cutoff. The canonical map on this cutoff is
invertible, and the derived torus evaluation transports the actual
target truncation on the original shifted Hom groups.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme

universe w w' w'' u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original singular torus map is bijective on shifted Hom from
every smooth transfer representable, in every integer degree. -/
theorem singularSheafDerivedTorusSectionsMap_bijective_on_transferRepresentable
    (X : SmoothSite (Spec (.of k))) (P : PresheafWithTransfers.{u + 1} k) (p : ℤ) :
    Function.Bijective (fun f :
      (DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj (Cor.mk X)) ⟶
        (DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0))⟦p⟧ =>
      f ≫ (singularSheafDerivedTorusSectionsMap k P)⟦p⟧') := by
  let G := SmoothSite.multiplicativeGroupObject (Spec (.of k))
  let XT := SmoothSite.product X G
  obtain ⟨d₀, h₀⟩ := SmoothSite.exists_nat_topologicalKrullDim_le k X
  obtain ⟨d₁, h₁⟩ := SmoothSite.exists_nat_topologicalKrullDim_le k XT
  let d := max d₀ d₁
  have hd₀ : (d₀ : WithBot ℕ∞) ≤ d :=
    WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (le_max_left d₀ d₁))
  have hd₁ : (d₁ : WithBot ℕ∞) ≤ d :=
    WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (le_max_right d₀ d₁))
  let W := (transferRepresentable k).obj (Cor.mk X)
  let : HasProjectiveDimensionLE W d :=
    transferRepresentable_hasProjectiveDimensionLE_of_krullDim_le k X d (h₀.trans hd₀)
  let : HasProjectiveDimensionLE ((transferRepresentable k).obj (Cor.mk XT)) d :=
    transferRepresentable_hasProjectiveDimensionLE_of_krullDim_le k XT d (h₁.trans hd₁)
  let E := DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0)
  let K := DerivedCategory.Q.obj (singularSheafCochainComplex k P 0)
  let R := torusSectionsDerivedFunctor k
  let a : ℤ := p - (d : ℤ)
  let L := (DerivedCategory.TStructure.t.truncGE a).obj K
  let π : K ⟶ L := (DerivedCategory.TStructure.t.truncGEπ a).app K
  let W₀ := (DerivedCategory.singleFunctor _ 0).obj W
  let f (x : W₀ ⟶ E⟦p⟧) := x ≫ (singularSheafDerivedTorusSectionsMap k P)⟦p⟧'
  let g (y : W₀ ⟶ (R.obj K)⟦p⟧) := y ≫ (R.map π)⟦p⟧'
  have hg : Function.Bijective g :=
    bijective_comp_torusSectionsDerived_map_truncGEπ k X K d p
  change Function.Bijective f
  apply (Function.Bijective.of_comp_iff' hg f).mp
  have h := singularSheafDerivedTorusSectionsMap_comp_cutoff_bijective k P W d p
  change Function.Bijective (fun x : W₀ ⟶ E⟦p⟧ =>
    x ≫ (singularSheafDerivedTorusSectionsMap k P ≫ R.map π)⟦p⟧') at h
  simpa only [Function.comp_def, f, g, Functor.map_comp, Category.assoc] using h

/-- The actual singular torus comparison is invertible in the original
unbounded derived category. -/
theorem isIso_singularSheafDerivedTorusSectionsMap
    (P : PresheafWithTransfers.{u + 1} k) :
    IsIso (singularSheafDerivedTorusSectionsMap k P) :=
  isIso_of_bijective_hom_transferRepresentable k _ (fun X p =>
    singularSheafDerivedTorusSectionsMap_bijective_on_transferRepresentable k X.toSmoothSite P p)

end AlgebraicGeometry.SheafWithTransfers

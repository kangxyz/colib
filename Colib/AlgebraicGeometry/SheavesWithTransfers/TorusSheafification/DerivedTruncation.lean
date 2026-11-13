/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.Acyclic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedWindow

/-!
# The actual singular comparison on truncated inputs

The derived torus sections of the truncated target retain its lower
bound. The canonical singular comparison therefore factors through
the corresponding source truncation. The same map on shifted Hom is
read through the original finite projective-dimension cutoff.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe w u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- Factor the actual comparison through the original source truncation,
with the derived torus sections of the actual truncated target. -/
def singularSheafDerivedTorusSectionsTruncationMap (P : PresheafWithTransfers.{u + 1} k)
    (a : ℤ) :
    (DerivedCategory.TStructure.t.truncGE a).obj
        (DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0)) ⟶
      (torusSectionsDerivedFunctor k).obj ((DerivedCategory.TStructure.t.truncGE a).obj
        (DerivedCategory.Q.obj (singularSheafCochainComplex k P 0))) := by
  let E := DerivedCategory.Q.obj (singularSheafCochainComplex k P 0)
  let R := torusSectionsDerivedFunctor k
  let L := (DerivedCategory.TStructure.t.truncGE a).obj E
  let : L.IsGE a := inferInstanceAs (((DerivedCategory.TStructure.t.truncGE a).obj E).IsGE a)
  let : (R.obj L).IsGE a := torusSectionsDerived_isGE k L a
  exact DerivedCategory.TStructure.t.descTruncGE
    (singularSheafDerivedTorusSectionsMap k P ≫
      R.map ((DerivedCategory.TStructure.t.truncGEπ a).app E)) a

/-- The factorization retains the actual map and the two canonical
truncation projections. -/
@[reassoc]
theorem singularSheafDerivedTorusSectionsTruncationMap_comp
    (P : PresheafWithTransfers.{u + 1} k) (a : ℤ) :
    (DerivedCategory.TStructure.t.truncGEπ a).app
        (DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0)) ≫
      singularSheafDerivedTorusSectionsTruncationMap k P a =
    singularSheafDerivedTorusSectionsMap k P ≫ (torusSectionsDerivedFunctor k).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app
        (DerivedCategory.Q.obj (singularSheafCochainComplex k P 0))) := by
  let E := DerivedCategory.Q.obj (singularSheafCochainComplex k P 0)
  let R := torusSectionsDerivedFunctor k
  let L := (DerivedCategory.TStructure.t.truncGE a).obj E
  let : L.IsGE a := inferInstanceAs (((DerivedCategory.TStructure.t.truncGE a).obj E).IsGE a)
  let : (R.obj L).IsGE a := torusSectionsDerived_isGE k L a
  exact DerivedCategory.TStructure.t.π_descTruncGE
    (singularSheafDerivedTorusSectionsMap k P ≫
      R.map ((DerivedCategory.TStructure.t.truncGEπ a).app E)) a

/-- The shifted Hom comparison to the derived torus of the truncated target
can be computed using the actual factorization on the source truncation. -/
theorem singularSheafDerivedTorusSectionsTruncationMap_bijective_iff
    (P : PresheafWithTransfers.{u + 1} k) (W : SheafWithTransfers.{u + 1} k)
    (d : ℕ) [HasProjectiveDimensionLE W d] (p : ℤ) :
    let a : ℤ := p - (d : ℤ)
    let E := DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0)
    let L := DerivedCategory.Q.obj (singularSheafCochainComplex k P 0)
    let R := torusSectionsDerivedFunctor k
    let f := singularSheafDerivedTorusSectionsMap k P ≫
      R.map ((DerivedCategory.TStructure.t.truncGEπ a).app L)
    Function.Bijective (fun x : (DerivedCategory.singleFunctor _ 0).obj W ⟶ E⟦p⟧ =>
      x ≫ f⟦p⟧') ↔
    Function.Bijective (fun x : (DerivedCategory.singleFunctor _ 0).obj W ⟶
        ((DerivedCategory.TStructure.t.truncGE a).obj E)⟦p⟧ =>
      x ≫ (singularSheafDerivedTorusSectionsTruncationMap k P a)⟦p⟧') := by
  let a : ℤ := p - (d : ℤ)
  let E := DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0)
  let L := DerivedCategory.Q.obj (singularSheafCochainComplex k P 0)
  let R := torusSectionsDerivedFunctor k
  let f := singularSheafDerivedTorusSectionsMap k P ≫
    R.map ((DerivedCategory.TStructure.t.truncGEπ a).app L)
  let S := (DerivedCategory.singleFunctor _ 0).obj W
  let π := (DerivedCategory.TStructure.t.truncGEπ a).app E
  let cutoff (x : S ⟶ E⟦p⟧) := x ≫ π⟦p⟧'
  let map (x : S ⟶ E⟦p⟧) := x ≫ f⟦p⟧'
  let truncatedMap (x : S ⟶ ((DerivedCategory.TStructure.t.truncGE a).obj E)⟦p⟧) :=
    x ≫ (singularSheafDerivedTorusSectionsTruncationMap k P a)⟦p⟧'
  have hBij : Function.Bijective cutoff :=
    DerivedCategory.bijective_comp_truncGEπ_of_hasProjectiveDimensionLE W d E p
  have h : truncatedMap ∘ cutoff = map := by
    funext x
    change (x ≫ π⟦p⟧') ≫ (singularSheafDerivedTorusSectionsTruncationMap k P a)⟦p⟧' =
      x ≫ f⟦p⟧'
    simpa only [f, π, Functor.map_comp, Category.assoc] using
      congrArg (fun g => x ≫ g⟦p⟧') (singularSheafDerivedTorusSectionsTruncationMap_comp k P a)
  change Function.Bijective map ↔ Function.Bijective truncatedMap
  rw [← h]
  exact Function.Bijective.of_comp_iff truncatedMap hBij

end AlgebraicGeometry.SheafWithTransfers

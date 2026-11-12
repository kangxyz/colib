/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.Singular
public import Colib.CategoryTheory.Sites.Hypercohomology.FiniteWindow
import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# The derived comparison on the original singular complexes

Extension places the signed torus comparison in the original cochain
degrees. The actual derived unit supplies the target map. Finite
projective dimension identifies its action on a shifted Hom group with
the action after the two canonical lower truncations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe w u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The actual torus comparison in weight-zero cochain placement. -/
def singularSheafCochainTorusSectionsMap (P : PresheafWithTransfers.{u + 1} k) :
    singularSheafCochainComplex k (torusSections P) 0 ⟶
      ((torusSectionsFunctor k).mapHomologicalComplex (.up ℤ)).obj
        (singularSheafCochainComplex k P 0) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let a := nisnevichSheafify k
  let b : SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k := torusSectionsFunctor k
  exact (Stacks.DerivedIndexing.mapExtendIso a e (singularComplex (torusSections P))).inv ≫
    (e.extendFunctor _).map (singularSheafTorusSectionsMap k P) ≫
    (Stacks.DerivedIndexing.mapExtendIso b e (singularSheafComplex k P)).hom ≫
    (b.mapHomologicalComplex (.up ℤ)).map
      (Stacks.DerivedIndexing.mapExtendIso a e (singularComplex P)).hom

variable [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- The actual singular torus comparison followed by the genuine total
right-derived unit. -/
def singularSheafDerivedTorusSectionsMap (P : PresheafWithTransfers.{u + 1} k) :
    DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0) ⟶
      (torusSectionsDerivedFunctor k).obj
        (DerivedCategory.Q.obj (singularSheafCochainComplex k P 0)) :=
  DerivedCategory.Q.map (singularSheafCochainTorusSectionsMap k P) ≫
    (torusSectionsDerivedUnit k).app (singularSheafCochainComplex k P 0)

/-- On shifted Hom from a sheaf of finite projective dimension, bijectivity
of the actual derived comparison can be tested after lower truncation at
the same cutoff on source and target. -/
theorem singularSheafDerivedTorusSectionsMap_bijective_iff_truncGE
    (P : PresheafWithTransfers.{u + 1} k) (W : SheafWithTransfers.{u + 1} k)
    (d : ℕ) [HasProjectiveDimensionLE W d] (p : ℤ) :
    let a : ℤ := p - (d : ℤ)
    let E := DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0)
    let f := singularSheafDerivedTorusSectionsMap k P
    Function.Bijective (fun x : (DerivedCategory.singleFunctor _ 0).obj W ⟶ E⟦p⟧ =>
      x ≫ f⟦p⟧') ↔
    Function.Bijective (fun x : (DerivedCategory.singleFunctor _ 0).obj W ⟶
        ((DerivedCategory.TStructure.t.truncGE a).obj E)⟦p⟧ =>
      x ≫ ((DerivedCategory.TStructure.t.truncGE a).map f)⟦p⟧') := by
  let a : ℤ := p - (d : ℤ)
  let E := DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0)
  let L := (torusSectionsDerivedFunctor k).obj
    (DerivedCategory.Q.obj (singularSheafCochainComplex k P 0))
  let f : E ⟶ L := singularSheafDerivedTorusSectionsMap k P
  let S := (DerivedCategory.singleFunctor _ 0).obj W
  let t : Triangulated.TStructure (DerivedCategory (SheafWithTransfers.{u + 1} k)) :=
    DerivedCategory.TStructure.t
  let F := t.truncGE a
  let π := t.truncGEπ a
  let left (x : S ⟶ E⟦p⟧) := x ≫ (π.app E)⟦p⟧'
  let right (x : S ⟶ L⟦p⟧) := x ≫ (π.app L)⟦p⟧'
  let map (x : S ⟶ E⟦p⟧) := x ≫ f⟦p⟧'
  let truncatedMap (x : S ⟶ (F.obj E)⟦p⟧) := x ≫ (F.map f)⟦p⟧'
  have hl : Function.Bijective left :=
    DerivedCategory.bijective_comp_truncGEπ_of_hasProjectiveDimensionLE W d E p
  have hr : Function.Bijective right :=
    DerivedCategory.bijective_comp_truncGEπ_of_hasProjectiveDimensionLE W d L p
  have h : truncatedMap ∘ left = right ∘ map := by
    funext x
    have hn : f ≫ π.app L = π.app E ≫ F.map f := π.naturality f
    change (x ≫ (π.app E)⟦p⟧') ≫ (F.map f)⟦p⟧' =
      (x ≫ f⟦p⟧') ≫ (π.app L)⟦p⟧'
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun g : E ⟶ F.obj L => x ≫ g⟦p⟧') hn.symm
  change Function.Bijective map ↔ Function.Bijective truncatedMap
  calc
    Function.Bijective map ↔ Function.Bijective (right ∘ map) :=
      (Function.Bijective.of_comp_iff' hr map).symm
    _ ↔ Function.Bijective (truncatedMap ∘ left) := by rw [h]
    _ ↔ Function.Bijective truncatedMap := Function.Bijective.of_comp_iff truncatedMap hl

end AlgebraicGeometry.SheafWithTransfers

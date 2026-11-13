/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCylinderCochains
public import Colib.CategoryTheory.Sites.Simplicial.PointedParameterSmash
public import Colib.CategoryTheory.Sites.Simplicial.CylinderBoundary

/-!
# Naturality of the original pointed parameter comparisons

The original reduced product and the pointed quotient comparisons commute
with the actual maps of the first factor. Normalization and extension
retain those maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] (V : C)

private abbrev parameterCylinderInclusion (I : Cᵒᵖ ⥤ SSet.{w})
    (X : PointedSimplicialPresheaf.{w} C) :
    X.right ⨯ I ⟶ (parameterizedCylinder X I).right :=
  pushout.inl (intervalAxis X I) (terminal.from I)

/-- The original cylinder comparison is natural for the original pointed base maps. -/
theorem reducedFreeAbelianParameterCylinderIso_hom_naturality
    {X Y : PointedSimplicialPresheaf.{max v w} C} (f : X ⟶ Y) :
    (reducedFreeAbelian C).map (parameterizedCylinderMap f (liftedRepresentableInterval.{w} V)) ≫
        (reducedFreeAbelianParameterCylinderIso.{w} V Y).hom =
      (reducedFreeAbelianParameterCylinderIso.{w} V X).hom ≫
        (ParameterCoproduct.simplicialFunctor V _).map ((reducedFreeAbelian C).map f) := by
  let I := liftedRepresentableInterval.{w} V
  let F := freeAbelian.{max v w} C
  let R := reducedFreeAbelian.{max v w} C
  let Φ := ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}
  let e := freeAbelianParameterProductIso.{w} V
  let p := parameterizedCylinderMap f I
  let X₀ := parameterizedCylinder X I
  let Y₀ := parameterizedCylinder Y I
  let x := parameterCylinderInclusion I X
  let y := parameterCylinderInclusion I Y
  let a := F.map x ≫ reduction C X₀
  let b := F.map y ≫ reduction C Y₀
  let s := (reducedFreeAbelianParameterCylinderIso.{w} V X).hom
  let t := (reducedFreeAbelianParameterCylinderIso.{w} V Y).hom
  let : Epi a := epi_freeAbelianParameterCylinderInclusion I X
  have hp : x ≫ p.right = prod.map f.right (𝟙 I) ≫ y := pushout.inl_desc _ _ _
  have ha : a ≫ R.map p = F.map (prod.map f.right (𝟙 I)) ≫ b := by
    change (F.map x ≫ reduction C X₀) ≫ R.map p =
      F.map (prod.map f.right (𝟙 I)) ≫ F.map y ≫ reduction C Y₀
    rw [Category.assoc, reduction_naturality, ← F.map_comp_assoc, hp, F.map_comp_assoc]
  have hs : a ≫ s = e.hom.app X.right ≫ Φ.map (reduction C X) := by
    exact (Category.assoc _ _ _).trans (cylinderInclusion_reduction_comp_iso V X)
  have ht : b ≫ t = e.hom.app Y.right ≫ Φ.map (reduction C Y) := by
    exact (Category.assoc _ _ _).trans (cylinderInclusion_reduction_comp_iso V Y)
  have he : F.map (prod.map f.right (𝟙 I)) ≫ e.hom.app Y.right =
      e.hom.app X.right ≫ Φ.map (F.map f.right) :=
    e.hom.naturality f.right
  change R.map p ≫ t = s ≫ Φ.map (R.map f)
  apply (cancel_epi a).1
  calc
    _ = (a ≫ R.map p) ≫ t := (Category.assoc _ _ _).symm
    _ = F.map (prod.map f.right (𝟙 I)) ≫ b ≫ t :=
      (congrArg (· ≫ t) ha).trans (Category.assoc _ _ _)
    _ = F.map (prod.map f.right (𝟙 I)) ≫ e.hom.app Y.right ≫
        Φ.map (reduction C Y) := congrArg (F.map (prod.map f.right (𝟙 I)) ≫ ·) ht
    _ = (e.hom.app X.right ≫ Φ.map (F.map f.right)) ≫ Φ.map (reduction C Y) :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Φ.map (reduction C Y)) he)
    _ = e.hom.app X.right ≫ Φ.map (reduction C X ≫ R.map f) := by
      rw [Category.assoc, ← Φ.map_comp, reduction_naturality]
    _ = _ := by
      rw [Φ.map_comp, ← Category.assoc, ← hs, Category.assoc]

/-- Naturality of the comparison at the original normalized chains. -/
theorem reducedChainsParameterCylinderIso_hom_naturality
    {X Y : PointedSimplicialPresheaf.{max v w} C} (f : X ⟶ Y) :
    let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
    (reducedChains C).map (parameterizedCylinderMap f (liftedRepresentableInterval.{w} V)) ≫
        (reducedChainsParameterCylinderIso.{w} V Y).hom =
      (reducedChainsParameterCylinderIso.{w} V X).hom ≫
        (Φ.mapHomologicalComplex (.down ℕ)).map ((reducedChains C).map f) := by
  intro Φ
  let R := reducedFreeAbelian.{max v w} C
  let N := normalizedMooreComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max v w})
  let c := ComplexShape.down ℕ
  let E := normalizedMooreComplexCompMapHomologicalComplexIso Φ
  let g := R.map (parameterizedCylinderMap f (liftedRepresentableInterval.{w} V))
  let u := R.map f
  let a := (reducedFreeAbelianParameterCylinderIso.{w} V X).hom
  let b := (reducedFreeAbelianParameterCylinderIso.{w} V Y).hom
  let F := ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}
  have hg : g ≫ b = a ≫ F.map u :=
    reducedFreeAbelianParameterCylinderIso_hom_naturality V f
  have h : N.map (F.map u) ≫ E.inv.app (R.obj Y) =
      E.inv.app (R.obj X) ≫ (Φ.mapHomologicalComplex c).map (N.map u) :=
    E.inv.naturality u
  rw [reducedChainsParameterCylinderIso_hom_eq, reducedChainsParameterCylinderIso_hom_eq]
  change N.map g ≫ N.map b ≫ E.inv.app (R.obj Y) =
    (N.map a ≫ E.inv.app (R.obj X)) ≫ (Φ.mapHomologicalComplex c).map (N.map u)
  calc
    _ = N.map (g ≫ b) ≫ E.inv.app (R.obj Y) := (N.map_comp_assoc _ _ _).symm
    _ = N.map (a ≫ F.map u) ≫ E.inv.app (R.obj Y) :=
      congrArg (fun t => N.map t ≫ E.inv.app (R.obj Y)) hg
    _ = N.map a ≫ (N.map (F.map u) ≫ E.inv.app (R.obj Y)) := N.map_comp_assoc _ _ _
    _ = _ := (congrArg (N.map a ≫ ·) h).trans (Category.assoc _ _ _).symm

/-- The cochain comparison is natural for the actual pointed cylinder maps. -/
theorem reducedPresheafCochainsParameterCylinderIso_hom_naturality
    {X Y : PointedSimplicialPresheaf.{max v w} C} (f : X ⟶ Y) :
    let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
    (reducedPresheafCochains C).map
        (parameterizedCylinderMap f (liftedRepresentableInterval.{w} V)) ≫
        (reducedPresheafCochainsParameterCylinderIso.{w} V Y).hom =
      (reducedPresheafCochainsParameterCylinderIso.{w} V X).hom ≫
        (Φ.mapHomologicalComplex (.up ℤ)).map ((reducedPresheafCochains C).map f) := by
  intro Φ
  let e := ComplexShape.embeddingUpIntLE 0
  let E := e.extendFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max v w})
  let a := (reducedChainsParameterCylinderIso.{w} V X).hom
  let b := (reducedChainsParameterCylinderIso.{w} V Y).hom
  let A := (reducedChains C).obj X
  let B := (reducedChains C).obj Y
  let g := (reducedChains C).map (parameterizedCylinderMap f (liftedRepresentableInterval.{w} V))
  let u := (reducedChains C).map f
  let Φ₀ := Φ.mapHomologicalComplex (.down ℕ)
  let Φ₁ := Φ.mapHomologicalComplex (.up ℤ)
  let d := e.mapExtendNatIso Φ
  have h : E.map (Φ₀.map u) ≫ d.inv.app B = d.inv.app A ≫ Φ₁.map (E.map u) :=
    d.inv.naturality u
  have hg : g ≫ b = a ≫ Φ₀.map u := reducedChainsParameterCylinderIso_hom_naturality V f
  rw [reducedPresheafCochainsParameterCylinderIso_hom_eq,
    reducedPresheafCochainsParameterCylinderIso_hom_eq]
  change E.map g ≫ E.map b ≫ d.inv.app B =
    (E.map a ≫ d.inv.app A) ≫ Φ₁.map (E.map u)
  calc
    _ = E.map (g ≫ b) ≫ d.inv.app B := (E.map_comp_assoc _ _ _).symm
    _ = E.map (a ≫ Φ₀.map u) ≫ d.inv.app B :=
      congrArg (fun t => E.map t ≫ d.inv.app B) hg
    _ = E.map a ≫ (E.map (Φ₀.map u) ≫ d.inv.app B) := E.map_comp_assoc _ _ _
    _ = _ := (congrArg (E.map a ≫ ·) h).trans (Category.assoc _ _ _).symm

/-- The quotient is natural on the actual pointed base maps. -/
theorem cylinderToParameterSmash_naturality
    {X X' : PointedSimplicialPresheaf.{w} C} (Y : PointedSimplicialPresheaf.{w} C)
    (f : X ⟶ X') :
    parameterizedCylinderMap f Y.right ≫ cylinderToParameterSmash X' Y =
      cylinderToParameterSmash X Y ≫ Under.smashMap f (𝟙 Y) := by
  let e := parameterizedCylinderMap f Y.right
  let a := parameterCylinderInclusion Y.right X
  let b := parameterCylinderInclusion Y.right X'
  let p := cylinderToParameterSmash X Y
  let q := cylinderToParameterSmash X' Y
  let g := Under.smashMap f (𝟙 Y)
  have he : a ≫ e.right = prod.map f.right (𝟙 Y.right) ≫ b := pushout.inl_desc _ _ _
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · change a ≫ e.right ≫ q.right = a ≫ p.right ≫ g.right
    calc
      _ = (prod.map f.right (𝟙 Y.right) ≫ b) ≫ q.right :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q.right) he)
      _ = prod.map f.right (𝟙 Y.right) ≫ Under.toSmash X' Y :=
        (Category.assoc _ _ _).trans (congrArg (prod.map f.right (𝟙 Y.right) ≫ ·)
          (cylinderInclusion_cylinderToParameterSmash X' Y))
      _ = Under.toSmash X Y ≫ g.right := (Under.toSmash_smashMap f (𝟙 Y)).symm
      _ = _ := (congrArg (· ≫ g.right)
        (cylinderInclusion_cylinderToParameterSmash X Y).symm).trans (Category.assoc _ _ _)
  · exact (Under.w (e ≫ q)).trans (Under.w (p ≫ g)).symm

end CategoryTheory.PointedSimplicialPresheaf

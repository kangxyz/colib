/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.CochainRepresentative
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.HomCongr

/-!
# Strict representative maps into derived Hom

For a K-injective coefficient, the strict pointed cochain representative
surjects onto the actual reduced derived Hom. Two strict maps give the
same class exactly when the corresponding cochain maps are homotopic.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe d w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- The strict cochain correspondence sends pointed precomposition to the original
cochain map on the source. -/
theorem pointedCochainRepresentativeCochainHomEquiv_precomp
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y)
    (g : Y ⟶ (pointedCochainRepresentative C J p).obj K) :
    pointedCochainRepresentativeCochainHomEquiv C J p K X (f ≫ g) =
      (reducedCochains C J).map f ≫
        pointedCochainRepresentativeCochainHomEquiv C J p K Y g := by
  let e := ComplexShape.embeddingUpIntLE 0
  let E := e.extendFunctor (Sheaf J AddCommGrpCat.{w})
  let T := K⟦p⟧
  let i := HomologicalComplex.ιTruncLE T e
  let a := reducedChainsForgetAdjunction.{w} C J
  let N := sheafifiedReducedChains.{w} C J
  let L := (CochainComplex.shiftedNonpositiveChains _ p).obj K
  change E.map ((a.homEquiv X L).symm (f ≫ g)) ≫ (T.truncLEIso e).inv ≫ i =
    E.map (N.map f) ≫ E.map ((a.homEquiv Y L).symm g) ≫ (T.truncLEIso e).inv ≫ i
  have h := a.homEquiv_naturality_left_symm (Y := L) f g
  calc
    _ = E.map (N.map f ≫ (a.homEquiv Y L).symm g) ≫ (T.truncLEIso e).inv ≫ i :=
      congrArg (fun k ↦ E.map k ≫ (T.truncLEIso e).inv ≫ i) h
    _ = _ := E.map_comp_assoc _ _ _

variable [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{w})]

/-- The class of a strict pointed map in the actual reduced hypercohomology group. -/
def pointedCochainRepresentativeDerivedMap
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    (X : PointedSimplicialPresheaf.{w} C)
    (f : X ⟶ (pointedCochainRepresentative C J p).obj K) :
    (reducedHypercohomology C J K p).obj (op X) :=
  DerivedCategory.Q.map (pointedCochainRepresentativeCochainHomEquiv C J p K X f) ≫
    (DerivedCategory.Q.commShiftIso p).hom.app K

theorem pointedCochainRepresentativeDerivedMap_precomp
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y)
    (g : Y ⟶ (pointedCochainRepresentative C J p).obj K) :
    pointedCochainRepresentativeDerivedMap C J p K X (f ≫ g) =
      (reducedHypercohomology C J K p).map f.op
        (pointedCochainRepresentativeDerivedMap C J p K Y g) := by
  rw [reducedHypercohomology_map_apply]
  let Q : _ ⥤ DerivedCategory.{d} (Sheaf J AddCommGrpCat.{w}) := DerivedCategory.Q
  let s := (Q.commShiftIso p).hom.app K
  change Q.map (pointedCochainRepresentativeCochainHomEquiv C J p K X (f ≫ g)) ≫ s =
    Q.map ((reducedCochains C J).map f) ≫
      Q.map (pointedCochainRepresentativeCochainHomEquiv C J p K Y g) ≫ s
  rw [pointedCochainRepresentativeCochainHomEquiv_precomp, Q.map_comp, Category.assoc]

private def representativeDerivedHomEquiv
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    (X : PointedSimplicialPresheaf.{w} C) :=
  let Q : _ ⥤ DerivedCategory.{d} (Sheaf J AddCommGrpCat.{w}) := DerivedCategory.Q
  let e : _ ≅ Q := DerivedCategory.quotientCompQhIso (Sheaf J AddCommGrpCat.{w})
  (e.app ((reducedCochains C J).obj X)).homCongr
    (e.app (K⟦p⟧) ≪≫ (Q.commShiftIso p).app K)

private theorem representativeDerivedMap_eq_homotopyMap
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    (X : PointedSimplicialPresheaf.{w} C)
    (f : X ⟶ (pointedCochainRepresentative C J p).obj K) :
    pointedCochainRepresentativeDerivedMap C J p K X f =
      representativeDerivedHomEquiv C J p K X
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          (pointedCochainRepresentativeCochainHomEquiv C J p K X f))) := by
  simp only [representativeDerivedHomEquiv, pointedCochainRepresentativeDerivedMap,
    Iso.homCongr_apply, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
    DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  exact (((DerivedCategory.quotientCompQhIso (Sheaf J AddCommGrpCat.{w})).app
    ((reducedCochains C J).obj X)).inv_hom_id_assoc _).symm

/-- Every derived class with K-injective coefficients is represented by a strict pointed map. -/
theorem pointedCochainRepresentativeDerivedMap_surjective
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) [K.IsKInjective]
    (X : PointedSimplicialPresheaf.{w} C) :
    Function.Surjective (pointedCochainRepresentativeDerivedMap C J p K X) := by
  intro z
  let H := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ)
  let e := representativeDerivedHomEquiv C J p K X
  obtain ⟨h, hh⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    (H.obj ((reducedCochains C J).obj X)) (K⟦p⟧)).2 (e.symm z)
  obtain ⟨g, hg⟩ := H.map_surjective h
  let a := pointedCochainRepresentativeCochainHomEquiv C J p K X
  refine ⟨a.symm g, ?_⟩
  rw [representativeDerivedMap_eq_homotopyMap]
  change e (DerivedCategory.Qh.map (H.map (a (a.symm g)))) = z
  rw [a.apply_symm_apply, hg, hh]
  exact e.apply_symm_apply z

/-- Equality of the strict-map classes is homotopy of the original cochain maps. -/
theorem pointedCochainRepresentativeDerivedMap_eq_iff
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) [K.IsKInjective]
    (X : PointedSimplicialPresheaf.{w} C)
    (f g : X ⟶ (pointedCochainRepresentative C J p).obj K) :
    pointedCochainRepresentativeDerivedMap C J p K X f =
        pointedCochainRepresentativeDerivedMap C J p K X g ↔
      Nonempty (Homotopy (pointedCochainRepresentativeCochainHomEquiv C J p K X f)
        (pointedCochainRepresentativeCochainHomEquiv C J p K X g)) := by
  rw [representativeDerivedMap_eq_homotopyMap, representativeDerivedMap_eq_homotopyMap]
  let a := pointedCochainRepresentativeCochainHomEquiv C J p K X
  let e := representativeDerivedHomEquiv C J p K X
  have hQ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj ((reducedCochains C J).obj X)) (K⟦p⟧)).1
  constructor
  · intro h
    exact ⟨HomotopyCategory.homotopyOfEq (a f) (a g) (hQ (e.injective h))⟩
  · rintro ⟨h⟩
    exact congrArg (fun k ↦ e (DerivedCategory.Qh.map k))
      (HomotopyCategory.eq_of_homotopy (a f) (a g) h)

end CategoryTheory.PointedSimplicialPresheaf

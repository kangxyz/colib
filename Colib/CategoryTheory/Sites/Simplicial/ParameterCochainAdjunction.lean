/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCylinderCochains
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints

import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective.AdjointAndProducts

/-!
# The parameter coproduct on homotopy classes of cochains

The degreewise fold is adjoint to the actual projection pullback. For a
K-injective target whose projection pullback is a quasi-isomorphism, exactness
of the parameter coproduct makes the reindexed target K-injective as well.
The projection is then invertible in the homotopy category, and the fold
induces a bijection on homotopy classes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v z w

namespace CategoryTheory.PointedSimplicialPresheaf.ParameterCoproduct

variable {C : Type u} [Category.{v} C] (V : C) [HasBinaryProducts C]
  (A : Type z) [Category.{w} A] [Abelian A] [HasCoproducts.{v} A]

/-- Restrict cochains degreewise along the actual first projection. -/
def homologicalProjectionPullback {ι : Type*} (c : ComplexShape ι) :
    𝟭 (HomologicalComplex (Cᵒᵖ ⥤ A) c) ⟶ (reindex V A).mapHomologicalComplex c :=
  (Functor.mapHomologicalComplexIdIso _ c).inv ≫
    (projectionPullback V A).mapHomologicalComplex c

omit [HasCoproducts.{v} A] in
@[simp]
theorem homologicalProjectionPullback_app_f {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (Cᵒᵖ ⥤ A) c) (i : ι) :
    ((homologicalProjectionPullback V A c).app K).f i = (projectionPullback V A).app (K.X i) := by
  simp [homologicalProjectionPullback]

set_option backward.isDefEq.respectTransparency false in
/-- The transpose of the cochain fold is the original projection pullback. -/
theorem homEquiv_homologicalFold {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (Cᵒᵖ ⥤ A) c) :
    ((adjunction V A).mapHomologicalComplexAdjunction c).homEquiv K K
      ((homologicalFold V A c).app K) = (homologicalProjectionPullback V A c).app K := by
  apply HomologicalComplex.hom_ext
  intro i
  change (adjunction V A).homEquiv (K.X i) (K.X i) (((homologicalFold V A c).app K).f i) =
    ((homologicalProjectionPullback V A c).app K).f i
  rw [homologicalFold_app_f, homologicalProjectionPullback_app_f, homEquiv_fold]

variable [AB4OfSize.{v} A]

set_option backward.isDefEq.respectTransparency false in
/-- Invertible projection pullback for a K-injective target makes the
actual fold induce a bijection on homotopy classes out of any source. -/
theorem bijective_precomp_homologicalFold
    (K I : CochainComplex (Cᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
    (hI : QuasiIso ((homologicalProjectionPullback V A (.up ℤ)).app I)) :
    let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ A) (.up ℤ)
    Function.Bijective (fun f : Q.obj K ⟶ Q.obj I ↦
      Q.map ((homologicalFold V A (.up ℤ)).app K) ≫ f) := by
  let c := ComplexShape.up ℤ
  let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ A) c
  let R := reindex V A
  let adj := adjunction V A
  let adjc := adj.mapHomologicalComplexAdjunction c
  let adjh := adj.mapHomotopyCategoryAdjunction c
  let π := homologicalProjectionPullback V A c
  let η := homologicalFold V A c
  have : CochainComplex.IsKInjective ((R.mapHomologicalComplex (.up ℤ)).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact R (functor V A) adj I
  have : IsIso (Q.map (π.app I)) := by
    have he := (CochainComplex.IsKInjective.quasiIso_iff (K := I)
      (L := (R.mapHomologicalComplex (.up ℤ)).obj I) (π.app I)).mp hI
    rw [← HomotopyCategory.inverseImage_quotient_isomorphisms,
      MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] at he
    exact he
  have hη : (adjh.homEquiv (Q.obj K) (Q.obj K)) (Q.map (η.app K)) = Q.map (π.app K) := by
    rw [← homEquiv_homologicalFold V A c K, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change Q.map (adjc.unit.app K) ≫ Q.map ((R.mapHomologicalComplex c).map (η.app K)) =
      Q.map (adjc.unit.app K ≫ (R.mapHomologicalComplex c).map (η.app K))
    exact (Q.map_comp _ _).symm
  let post : (Q.obj K ⟶ Q.obj I) ≃ (Q.obj K ⟶ (R.mapHomotopyCategory c).obj (Q.obj I)) := {
    toFun f := f ≫ Q.map (π.app I)
    invFun f := f ≫ inv (Q.map (π.app I))
    left_inv f := by simp
    right_inv f := by simp }
  let e := post.trans (adjh.homEquiv (Q.obj K) (Q.obj I)).symm
  have he : (fun f : Q.obj K ⟶ Q.obj I ↦ Q.map (η.app K) ≫ f) = ⇑e := by
    funext f
    let a := adjh.homEquiv (Q.obj K) (Q.obj I)
    apply a.injective
    have hpost : a (e f) = f ≫ Q.map (π.app I) := a.apply_symm_apply _
    calc
      a (Q.map (η.app K) ≫ f) =
          (adjh.homEquiv (Q.obj K) (Q.obj K)) (Q.map (η.app K)) ≫
            (R.mapHomotopyCategory c).map f := adjh.homEquiv_naturality_right _ _
      _ = Q.map (π.app K) ≫ (R.mapHomotopyCategory c).map f :=
        congrArg (fun t ↦ t ≫ (R.mapHomotopyCategory c).map f) hη
      _ = f ≫ Q.map (π.app I) := by
        obtain ⟨g, rfl⟩ := Q.map_surjective f
        change Q.map (π.app K) ≫ Q.map ((R.mapHomologicalComplex c).map g) =
          Q.map g ≫ Q.map (π.app I)
        rw [← Q.map_comp, ← Q.map_comp]
        exact congrArg Q.map (π.naturality g).symm
      _ = a (e f) := hpost.symm
  change Function.Bijective (fun f : Q.obj K ⟶ Q.obj I ↦ Q.map (η.app K) ≫ f)
  rw [he]
  exact e.bijective

end CategoryTheory.PointedSimplicialPresheaf.ParameterCoproduct

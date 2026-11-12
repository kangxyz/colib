/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCochainAdjunction
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Algebra.Homology.Functor

/-!
# Evaluating projection pullback on a complex of sheaves

Evaluating the parameter projection pullback on the underlying presheaf
complex gives the map of literal sections complexes induced by the first
projection. If this restriction is invertible on homology in every degree
and at every site object, the underlying presheaf map is a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v z w

namespace CategoryTheory.PointedSimplicialPresheaf.ParameterCoproduct

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  (J : GrothendieckTopology C) (V : C) (A : Type z) [Category.{w} A] [Abelian A]

/-- Evaluation of the underlying projection map is the original restriction
between the degreewise sections complexes. -/
theorem evaluation_map_homologicalProjectionPullback_sheafToPresheaf
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex (Sheaf J A) c) (U : C) :
    (((CategoryTheory.evaluation Cᵒᵖ A).obj (op U)).mapHomologicalComplex c).map
        ((homologicalProjectionPullback V A c).app
          (((sheafToPresheaf J A).mapHomologicalComplex c).obj K)) =
      (((sheafSections J A).map (prod.fst : U ⨯ V ⟶ U).op).mapHomologicalComplex c).app K := by
  apply HomologicalComplex.hom_ext
  intro i
  let L := ((sheafToPresheaf J A).mapHomologicalComplex c).obj K
  change (((homologicalProjectionPullback V A c).app L).f i).app (op U) =
    ((sheafSections J A).map (prod.fst : U ⨯ V ⟶ U).op).app (K.X i)
  exact (congrArg (fun α ↦ α.app (op U)) (homologicalProjectionPullback_app_f V A c L i)).trans
    (projectionPullback_app_app V A (L.X i) U)

/-- Objectwise homology invariance of the literal sections restriction implies
that projection pullback of the underlying presheaf complex is a quasi-isomorphism. -/
theorem quasiIso_homologicalProjectionPullback_of_isIso_sections_homologyMap
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex (Sheaf J A) c)
    (h : ∀ (U : C) (i : ι),
      IsIso (HomologicalComplex.homologyMap
        ((((sheafSections J A).map (prod.fst : U ⨯ V ⟶ U).op).mapHomologicalComplex c).app K) i)) :
    QuasiIso ((homologicalProjectionPullback V A c).app
      (((sheafToPresheaf J A).mapHomologicalComplex c).obj K)) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
  rintro ⟨U⟩
  rw [evaluation_map_homologicalProjectionPullback_sheafToPresheaf J V A c K U]
  refine (quasiIso_iff _).mpr ?_
  intro i
  exact (quasiIsoAt_iff_isIso_homologyMap _ i).mpr (h U i)

end CategoryTheory.PointedSimplicialPresheaf.ParameterCoproduct

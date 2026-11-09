/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.Postcomposition
public import Colib.AlgebraicGeometry.Morphisms.Finite.CommonImage
public import Colib.AlgebraicGeometry.Morphisms.ClosedImmersion.BaseChange.ClosedImageBaseChange

/-!
# Common finite supports for the native correspondence Čech construction

A nonempty finite family of actual admissible ambient points has a common finite
closed image after target postcomposition. The family of all nonzero points of a
native `finiteCorrespondences` element is a direct application. Each actual graph
incidence then maps to the whole source-base-changed common support, preserving
its source projection and its original postcomposed target map.

The common image is the native scheme-theoretic image provided by the lower
finite-image construction. The incidence and its target pullback retain their
entire structure sheaves, including nilpotents. No reduction, flatness hypothesis,
cycle comparison or assertion about Tor coefficients is used. The statements
hold over an arbitrary base scheme with the displayed ambient hypotheses.

Adapted from `kangxyz/motivic` revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Cech/FiniteSupport.lean`.
The original custom generator model is replaced by native ambient points,
`integralComponentAt`, and the existing `correspondenceIncidence`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

section CommonImage

variable {S X V Y : Scheme.{u}}
  (x : X ⟶ S) (v : V ⟶ S) (y : Y ⟶ S) (q : V ⟶ Y) (hq : q ≫ y = v)

/-- A nonempty finite family of admissible native support points has one actual
closed image finite over the source after target postcomposition. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Cech/FiniteSupport.lean: exists_common_finite_image"
  "adaptation" "native admissible ambient points and their actual common finite closed image"]
theorem exists_common_finite_image [IsSeparated y] [LocallyOfFiniteType y]
    (s : Finset (pullback (C := Scheme) x v)) (hs : s.Nonempty)
    (ha : ∀ a ∈ s, IsFiniteCorrespondencePoint x v a) :
    ∃ (C : Scheme.{u}) (j : C ⟶ pullback x y),
      IsClosedImmersion j ∧ IsFinite (j ≫ pullback.fst x y) ∧
      ∀ a ∈ s, ∃ r : (integralComponentAt a).subscheme ⟶ C,
        r ≫ j = correspondenceGraphPostcompositionMap x v y q hq a := by
  apply AlgebraicGeometry.exists_finite_common_closed_image
    (fun a : pullback (C := Scheme) x v ↦ (integralComponentAt a).subscheme)
    (correspondenceGraphPostcompositionMap x v y q hq) (pullback.fst x y) s hs
  intro a ha'
  rw [correspondenceGraphPostcompositionMap_fst]
  exact (ha a ha').1

/-- Every nonzero support of an actual native finite correspondence factors
through the same finite closed image. The nonempty support hypothesis is explicit. -/
theorem exists_common_finite_image_of_correspondence
    [IsSeparated y] [LocallyOfFiniteType y]
    (c : finiteCorrespondences x v) (hne : c.1.support.Nonempty) :
    ∃ (C : Scheme.{u}) (j : C ⟶ pullback x y),
      IsClosedImmersion j ∧ IsFinite (j ≫ pullback.fst x y) ∧
      ∀ (a : pullback (C := Scheme) x v), a ∈ c.1.support →
        ∃ r : (integralComponentAt a).subscheme ⟶ C,
        r ≫ j = correspondenceGraphPostcompositionMap x v y q hq a := by
  classical
  obtain ⟨C, j, hj, hfinite, hr⟩ := exists_common_finite_image x v y q hq
    c.2.1.toFinset (c.2.1.toFinset_nonempty.mpr hne) (by
      intro a ha
      exact c.2.2 a (c.2.1.mem_toFinset.mp ha))
  refine ⟨C, j, hj, hfinite, ?_⟩
  intro a ha
  exact hr a (c.2.1.mem_toFinset.mpr ha)

end CommonImage

section GraphIncidence

variable {S X V Y U C : Scheme.{u}}
  (x : X ⟶ S) (v : V ⟶ S) (y : Y ⟶ S) (q : V ⟶ Y) (hq : q ≫ y = v)
  (a : pullback (C := Scheme) x v) (j : C ⟶ pullback x y)
  (r : (integralComponentAt a).subscheme ⟶ C)
  (hr : r ≫ j = correspondenceGraphPostcompositionMap x v y q hq a)
  (u : U ⟶ S) (g : U ⟶ X) (hg : g ≫ x = u) (t : genericPoints U)
  [IsSeparated x]

/-- The entire actual incidence with a source graph component maps to the whole
base change of the common support, without passing to any reduction. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Cech/FiniteSupport.lean: graphIncidenceToCommonSupport"
  "adaptation" "the whole native graph incidence maps to the whole common-support pullback"]
def graphIncidenceToCommonSupport :
    correspondenceIncidence u x v (correspondenceGraphMap u x g hg t.val) a ⟶
      pullback (j ≫ pullback.fst x y) g := by
  refine pullback.lift (pullback.snd _ _ ≫ r)
    (correspondenceIncidenceLeft u x v (correspondenceGraphMap u x g hg t.val) a) ?_
  calc
    _ = pullback.snd _ _ ≫ (integralComponentAt a).subschemeι ≫ pullback.fst x v := by
      rw [Category.assoc, ← Category.assoc r j, hr, correspondenceGraphPostcompositionMap_fst]
    _ = pullback.fst _ _ ≫
        (integralComponentAt (correspondenceGraphMap u x g hg t.val)).subschemeι ≫
          pullback.snd u x :=
      (pullback.condition
        (f := (integralComponentAt (correspondenceGraphMap u x g hg t.val)).subschemeι ≫
          pullback.snd u x)
        (g := (integralComponentAt a).subschemeι ≫ pullback.fst x v)).symm
    _ = _ := by
      have he := congrArg
        (fun f => pullback.fst
          ((integralComponentAt (correspondenceGraphMap u x g hg t.val)).subschemeι ≫
            pullback.snd u x)
          ((integralComponentAt a).subschemeι ≫ pullback.fst x v) ≫ f)
        (integralComponentAt_graphMap_snd u x g hg t.val)
      simpa only [correspondenceIncidenceLeft, Category.assoc] using he

/-- The common-support coordinate is the original incidence projection followed
by the given support factorization. -/
@[reassoc (attr := simp)]
theorem graphIncidenceToCommonSupport_fst :
    graphIncidenceToCommonSupport x v y q hq a j r hr u g hg t ≫
      pullback.fst (j ≫ pullback.fst x y) g = pullback.snd _ _ ≫ r :=
  pullback.lift_fst _ _ _

/-- The new-source coordinate is the original actual incidence source map. -/
@[reassoc (attr := simp)]
theorem graphIncidenceToCommonSupport_snd :
    graphIncidenceToCommonSupport x v y q hq a j r hr u g hg t ≫
      pullback.snd (j ≫ pullback.fst x y) g =
        correspondenceIncidenceLeft u x v (correspondenceGraphMap u x g hg t.val) a :=
  pullback.lift_snd _ _ _

/-- The common-support factor retains the original postcomposed target map. -/
@[reassoc]
theorem graphIncidenceToCommonSupport_target :
    graphIncidenceToCommonSupport x v y q hq a j r hr u g hg t ≫
      pullback.fst (j ≫ pullback.fst x y) g ≫ j ≫ pullback.snd x y =
        correspondenceIncidenceRight u x v (correspondenceGraphMap u x g hg t.val) a ≫ q := by
  rw [graphIncidenceToCommonSupport_fst_assoc,
    ← Category.assoc r j, hr, correspondenceGraphPostcompositionMap_snd]
  simp only [correspondenceIncidenceRight, Category.assoc]

/-- The literal map into the new ambient product is the original actual incidence
map followed by target postcomposition. -/
theorem graphIncidenceToCommonSupport_inclusion :
    graphIncidenceToCommonSupport x v y q hq a j r hr u g hg t ≫
      ClosedImageBaseChange.inclusion x y u g hg j =
        correspondenceIncidenceMap u x v (correspondenceGraphMap u x g hg t.val) a ≫
          pullback.map u v u y (𝟙 U) q (𝟙 S) (by simp) (by simpa using hq.symm) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, ClosedImageBaseChange.inclusion_fst,
      graphIncidenceToCommonSupport_snd, pullback.map, pullback.lift_fst,
      Category.comp_id, correspondenceIncidenceMap_fst]
  · simpa only [Category.assoc, ClosedImageBaseChange.inclusion_snd,
      pullback.map, pullback.lift_snd, correspondenceIncidenceMap_snd_assoc] using
      graphIncidenceToCommonSupport_target x v y q hq a j r hr u g hg t

/-- The entire graph-incidence factor is finite when the common support is finite
over the original source. No condition on its Tor coefficients is needed. -/
theorem isFinite_graphIncidenceToCommonSupport
    [IsFinite (j ≫ pullback.fst x y)] (ha : IsFiniteCorrespondencePoint x v a) :
    IsFinite (graphIncidenceToCommonSupport x v y q hq a j r hr u g hg t) := by
  have hfinite : IsFinite (correspondenceIncidenceLeft u x v
      (correspondenceGraphMap u x g hg t.val) a) :=
    isFinite_correspondenceIncidenceLeft u x v _ a
      (isFiniteCorrespondencePoint_graphMap u x g hg t) ha
  have : IsFinite (graphIncidenceToCommonSupport x v y q hq a j r hr u g hg t ≫
      pullback.snd (j ≫ pullback.fst x y) g) := by
    rw [graphIncidenceToCommonSupport_snd]
    exact hfinite
  exact IsFinite.of_comp _ (pullback.snd (j ≫ pullback.fst x y) g)

end GraphIncidence

end Stacks.Chow

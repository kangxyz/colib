/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Correspondences.Category
public import Colib.AlgebraicGeometry.Correspondences.Graph.Composition

/-!
# The actual graph functor from the smooth site to finite correspondences

An ordinary morphism is sent to the existing sum of its integral graph components.
The categorical identity is that same full componentwise diagonal graph. The actual
incidence Tor calculation for two graphs proves preservation of composition.

Implementation adapted from `motivic_source_a6805c4`,
`Motivic/AlgebraicGeometry/Correspondences/Graph/Functor.lean`, blob
`263528965f2fa92399925c7f2c50f9b1f8e4eaaa`. MVW (2006), Lecture 1, printed p. 6,
introduces the graph functor. Both objects and graph cycles here are the existing
native ones, and the field may be arbitrary; empty and disconnected objects are allowed.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

/-- Send every ordinary smooth-site morphism to its actual componentwise graph cycle. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Graph/Functor.lean: Cor.graphFunctor"
  "adaptation" "the actual native graph sum with proved Tor composition",
  colib_ref "MVW2006" "Lecture 1, printed p. 6, graph functor Sm to Cor"
  "adaptation" "ordinary morphisms over an arbitrary field, including disconnected objects",
  colib_tag "COL-0355"]
def graphFunctor : Scheme.SmoothSite (Spec (.of k)) ⥤ Cor k where
  obj X := ⟨X⟩
  map {X Y} φ := graphCorrespondenceOfComponents X.hom Y.hom φ.left
    (MorphismProperty.Over.w φ)
    (finite_genericPoints k (Cor.mk X))
  map_id X := rfl
  map_comp {X Y Z} φ ψ := by
    exact (incidenceTorPairing_graph_comp X.hom Y.hom Z.hom
      φ.left (MorphismProperty.Over.w φ) ψ.left (MorphismProperty.Over.w ψ)
      (finite_genericPoints k (Cor.mk X))
      (finite_genericPoints k (Cor.mk Y))).symm

@[simp]
theorem graphFunctor_obj (X : Scheme.SmoothSite (Spec (.of k))) :
    (graphFunctor k).obj X = Cor.mk X := rfl

/-- The morphism map is the actual native graph sum, not a formal correspondence symbol. -/
theorem graphFunctor_map {X Y : Scheme.SmoothSite (Spec (.of k))} (φ : X ⟶ Y) :
    (graphFunctor k).map φ = graphCorrespondenceOfComponents X.hom Y.hom φ.left
      (MorphismProperty.Over.w φ)
      (finite_genericPoints k (Cor.mk X)) := rfl

end AlgebraicGeometry.Cor

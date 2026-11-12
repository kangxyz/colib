/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.CommonImageCoverage
public import Colib.AlgebraicGeometry.Correspondences.Graph.Postcomposition
public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor

/-!
# Actual point coverage of a signed correspondence's common image

Take the finite family of precisely the nonzero native support components.
The genuine common scheme-theoretic image is finite over the source, and every
one of its points is covered by an actual point of an original support.

This is the geometric construction used by
`Motivic/Transfers/Sheaf/Germs/Cech/AutomaticSupport.lean`, blob
`7ddf39a231b42e6c99f735e432e45091c4f20dd8`, at motivic revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

/-- The common finite image is constructed from the original signed cycle's
nonzero supports, and retains point coverage by those same integral schemes. -/
theorem exists_common_finite_image_with_coverage
    (k : Type u) [Field k] {X Y V : Scheme.SmoothSite (Spec (.of k))}
    (α : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y)
    (hα : α.property.1.toFinset.Nonempty) :
    ∃ (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom),
      IsClosedImmersion j ∧ IsFinite (j ≫ pullback.fst X.hom Y.hom) ∧
      (∀ a ∈ α.val.support, ∃ r : (integralComponentAt a).subscheme ⟶ C,
        r ≫ j = correspondenceGraphPostcompositionMap X.hom V.hom Y.hom q.left
          (MorphismProperty.Over.w q) a) ∧
      ∀ z : C, ∃ a : α.property.1.toFinset,
        ∃ w : (integralComponentAt a.val).subscheme,
          j z = correspondenceGraphPostcompositionMap X.hom V.hom Y.hom q.left
            (MorphismProperty.Over.w q) a.val w := by
  classical
  obtain ⟨C, j, hj, hp, hr, hcover⟩ :=
    AlgebraicGeometry.exists_finite_common_closed_image_with_coverage
      (fun a : pullback (C := Scheme) X.hom V.hom => (integralComponentAt a).subscheme)
      (fun a => correspondenceGraphPostcompositionMap X.hom V.hom Y.hom q.left
        (MorphismProperty.Over.w q) a)
      (pullback.fst X.hom Y.hom) α.property.1.toFinset hα (by
        intro a ha
        rw [correspondenceGraphPostcompositionMap_fst]
        exact (α.property.2 a (α.property.1.mem_toFinset.mp ha)).1)
  refine ⟨C, j, hj, hp, ?_, ?_⟩
  · intro a ha
    exact hr a (α.property.1.mem_toFinset.mpr ha)
  · intro z
    obtain ⟨a, ha, w, hw⟩ := hcover z
    exact ⟨⟨a, ha⟩, w, hw⟩

end AlgebraicGeometry.Cor

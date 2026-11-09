/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphSupport
public import Colib.AlgebraicGeometry.Correspondences.Graph.Components

/-!
# Original native graph-component equations

The native integralComponentAt of an actual graph image point lies in the
original graph, and its source image is exactly the closure of the original
generic point. Both statements use the existing native component isomorphism
for a closed immersion. This is the original component data needed by the
motivic Exterior/Simplex/Graph comparison, without an auxiliary generator model.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow

variable {S : Scheme.{u}} (X Y : SmoothSite S) (φ : X ⟶ Y) (t : genericPoints X.left)

/-- The native integral closed support at the original graph image point. -/
abbrev nativeGraphComponent : (pullback X.hom Y.hom).IdealSheafData :=
  integralComponentAt
    (correspondenceGraphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ) t.val)

/-- The original component satisfies the actual graph relation as a scheme-map equality. -/
theorem nativeGraphComponent_projection_graph :
    exteriorSupport_sourceProjection X Y (nativeGraphComponent X Y φ t) ≫ φ.left =
      exteriorSupport_targetProjection X Y (nativeGraphComponent X Y φ t) := by
  let j := correspondenceGraphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ)
  let : IsClosedImmersion j :=
    isClosedImmersion_correspondenceGraphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ)
  obtain ⟨e, he⟩ := exists_iso_integralComponentAt_comp j t.val
  apply (cancel_epi e.hom).mp
  change e.hom ≫ ((integralComponentAt (j t.val)).subschemeι ≫ pullback.fst _ _ ≫ φ.left) =
    e.hom ≫ ((integralComponentAt (j t.val)).subschemeι ≫ pullback.snd _ _)
  simp only [← Category.assoc, he]
  simp only [Category.assoc, j, correspondenceGraphMap_fst,
    correspondenceGraphMap_snd, Category.id_comp]

/-- The actual source image is the original generic-point closure. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/Graph.lean:121-147"
  "adaptation" "Original native graph component has its exact source-component image"]
theorem nativeGraphComponent_source_range :
    Set.range (exteriorSupport_sourceProjection X Y (nativeGraphComponent X Y φ t)) =
      closure ({t.val} : Set X.left) := by
  let j := correspondenceGraphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ)
  let : IsClosedImmersion j :=
    isClosedImmersion_correspondenceGraphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ)
  obtain ⟨e, he⟩ := exists_iso_integralComponentAt_comp j t.val
  have hf : e.hom ≫ (integralComponentAt (j t.val)).subschemeι ≫ pullback.fst X.hom Y.hom =
      (integralComponentAt t.val).subschemeι := by
    simpa only [Category.assoc, j, correspondenceGraphMap_fst, Category.comp_id] using
      congrArg (fun a => a ≫ pullback.fst X.hom Y.hom) he
  have hr := range_eq_range_of_surjective (integralComponentAt t.val).subschemeι
    ((integralComponentAt (j t.val)).subschemeι ≫ pullback.fst X.hom Y.hom) e.hom hf
  change Set.range ((integralComponentAt (j t.val)).subschemeι ≫
    pullback.fst X.hom Y.hom) = _
  calc
    _ = Set.range (integralComponentAt t.val).subschemeι := hr.symm
    _ = closure ({t.val} : Set X.left) := by
      rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]

end Stacks.Chow

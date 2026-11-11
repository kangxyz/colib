/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.ClosedEndpointCycle

/-!
# Genuine whole finite-flat span specialization by the native affine section

For a whole finite-flat family whose actual paired map is closed, native graph
precomposition equals the existing `Cor.ofFiniteFlatSpan` of its whole Cartesian
endpoint. The source, target, finite pushforward, original generic multiplicities
and native additive cylinder are unchanged. The specialization at zero and one
is literal and requires no flatness of the individual components over the source.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

open Stacks.Chow Scheme Scheme.AffineLineFiber Scheme.PolynomialSectionPencil
open Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))} {D : Scheme.{u}}

/-- The existing paired-span constructor recovers its actual ambient map. -/
theorem ofFiniteFlatSpan_pair
    (m : D ⟶ pullback Y.hom Z.hom) [IsFinite m]
    [IsFinite (m ≫ pullback.fst Y.hom Z.hom)] [Flat (m ≫ pullback.fst Y.hom Z.hom)] :
    letI := isNoetherian_of_finiteType (m ≫ pullback.fst Y.hom Z.hom)
    ofFiniteFlatSpan (m ≫ pullback.fst Y.hom Z.hom) (m ≫ pullback.snd Y.hom Z.hom)
      (by simp only [Category.assoc, pullback.condition]) =
        finiteFlatSpanFundamental Y.hom Z.hom m := by
  haveI := isNoetherian_of_finiteType (m ≫ pullback.fst Y.hom Z.hom)
  apply Subtype.ext
  rw [ofFiniteFlatSpan_val]
  congr 1
  apply pullback.hom_ext <;> simp

variable (φ : X ⟶ Y) (m : D ⟶ pullback Y.hom Z.hom)
  [IsClosedImmersion m] [IsFinite (m ≫ pullback.fst Y.hom Z.hom)]
  [Flat (m ≫ pullback.fst Y.hom Z.hom)]

/-- The actual endpoint span legs commute over the original ground field. -/
theorem wholeEndpoint_base :
    pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom) ≫ X.hom =
      (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom) ≫
        m ≫ pullback.snd Y.hom Z.hom) ≫ Z.hom := by
  rw [← MorphismProperty.Over.w φ, ← Category.assoc, pullback.condition]
  simp only [Category.assoc, pullback.condition]

/-- The actual whole Cartesian endpoint span, not a selected component or its reduction. -/
theorem graph_comp_ofFiniteFlatSpan_pair_of_cartesian_endpoint
    (q : Y.left ⟶ Spec (.of (Polynomial k))) [Flat q] (a : k)
    (H : IsPullback φ.left X.hom q (point a)) :
    (graphFunctor k).map φ ≫
      ofFiniteFlatSpan (m ≫ pullback.fst Y.hom Z.hom) (m ≫ pullback.snd Y.hom Z.hom)
        (by simp only [Category.assoc, pullback.condition]) =
      ofFiniteFlatSpan (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
        (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom) ≫
          m ≫ pullback.snd Y.hom Z.hom) (wholeEndpoint_base φ m) := by
  haveI := isNoetherian_of_finiteType (m ≫ pullback.fst Y.hom Z.hom)
  haveI := isNoetherian_of_finiteType
    (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
  let e := closedSupportEndpointIso X.hom Y.hom Z.hom φ.left q a H m
  let n := pullback.lift
    (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
    (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom) ≫
      m ≫ pullback.snd Y.hom Z.hom) (wholeEndpoint_base φ m)
  haveI : IsFinite n := isFinite_spanMap _ _ _
  have he : e.hom ≫ n = closedSupportEndpointMap X.hom Y.hom Z.hom φ.left
      (MorphismProperty.Over.w φ) q a H m := by
    apply pullback.hom_ext
    · simpa only [n, Category.assoc, pullback.lift_fst] using
        (closedSupportEndpointMap_fst X.hom Y.hom Z.hom φ.left
          (MorphismProperty.Over.w φ) q a H m).symm
    · simp only [n, Category.assoc, pullback.lift_snd,
        closedSupportEndpointMap_snd, e, closedSupportEndpointIso_total_assoc]
  rw [ofFiniteFlatSpan_pair]
  apply Subtype.ext
  rw [graph_comp_closedFiniteFlatSpan_val_eq_whole_endpoint φ q a H m,
    ofFiniteFlatSpan_val]
  change _ = finiteCyclePushforward n _
  rw [← finiteCyclePushforward_fundamentalCycle_iso e,
    finiteCyclePushforward_comp_apply, he]

variable (U V : SmoothSite (Spec (.of k))) (r : k)
  (m : D ⟶ pullback (affineLineCylinder.obj U).hom V.hom)
  [IsClosedImmersion m]
  [IsFinite (m ≫ pullback.fst (affineLineCylinder.obj U).hom V.hom)]
  [Flat (m ≫ pullback.fst (affineLineCylinder.obj U).hom V.hom)]

/-- Literal native affine-section specialization of the entire finite-flat span. -/
theorem nativeSection_comp_ofFiniteFlatSpan_pair :
    let σ := nativeAffineSection (.of k) U r
    (graphFunctor k).map σ ≫
      ofFiniteFlatSpan (m ≫ pullback.fst (affineLineCylinder.obj U).hom V.hom)
        (m ≫ pullback.snd (affineLineCylinder.obj U).hom V.hom)
        (by simp only [Category.assoc, pullback.condition]) =
      ofFiniteFlatSpan
        (pullback.fst σ.left (m ≫ pullback.fst (affineLineCylinder.obj U).hom V.hom))
        (pullback.snd σ.left (m ≫ pullback.fst (affineLineCylinder.obj U).hom V.hom) ≫
          m ≫ pullback.snd (affineLineCylinder.obj U).hom V.hom)
        (wholeEndpoint_base σ m) := by
  exact graph_comp_ofFiniteFlatSpan_pair_of_cartesian_endpoint
    (nativeAffineSection (.of k) U r) m
    ((nativeParameterIso (.of k) U).hom ≫
      pullback.snd U.hom
        (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) r
    (nativeSection_affineLine_isPullback r U)

end AlgebraicGeometry.Cor

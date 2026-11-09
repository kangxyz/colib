/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor
public import Colib.AlgebraicGeometry.Correspondences.Graph.Postcomposition
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual target pushforward and closed-immersion graph monomorphisms

The ambient map induced by a target morphism is Mathlib's pullback map. When it
is finite, composition with the actual full graph is its native finite cycle
pushforward, on every signed correspondence. Closed-immersion graph cancellation
then uses the existing native finite-pushforward injectivity theorem.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Coproducts/Binary.lean`,
`graphTargetMap`, `toIntegralCycle_comp_graph_of_finite`, and
`graph_map_mono_of_isClosedImmersion`. The original custom `IntegralCycle` is
replaced by the existing native `AlgebraicCycle` subgroup, not compared to a new
presentation. Arbitrary fields and empty or disconnected smooth schemes are allowed.

Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin

attribute [local instance] isIntegral_integralComponentAt

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

/-- The literal product map induced by an ordinary map of targets. -/
def graphTargetMap (X : Scheme.SmoothSite (Spec (.of k)))
    {Y Z : Scheme.SmoothSite (Spec (.of k))} (q : Y ⟶ Z) :
    pullback X.hom Y.hom ⟶ pullback X.hom Z.hom :=
  pullback.map X.hom Y.hom X.hom Z.hom (𝟙 X.left) q.left (𝟙 _)
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem graphTargetMap_fst (X : Scheme.SmoothSite (Spec (.of k)))
    {Y Z : Scheme.SmoothSite (Spec (.of k))} (q : Y ⟶ Z) :
    graphTargetMap k X q ≫ pullback.fst X.hom Z.hom =
      pullback.fst X.hom Y.hom := by
  simp [graphTargetMap, pullback.map]

@[reassoc (attr := simp)]
theorem graphTargetMap_snd (X : Scheme.SmoothSite (Spec (.of k)))
    {Y Z : Scheme.SmoothSite (Spec (.of k))} (q : Y ⟶ Z) :
    graphTargetMap k X q ≫ pullback.snd X.hom Z.hom =
      pullback.snd X.hom Y.hom ≫ q.left := by
  simp [graphTargetMap, pullback.map]

instance graphTargetMap_isClosedImmersion (X : Scheme.SmoothSite (Spec (.of k)))
    {Y Z : Scheme.SmoothSite (Spec (.of k))} (q : Y ⟶ Z) [IsClosedImmersion q.left] :
    IsClosedImmersion (graphTargetMap k X q) := by
  let : MorphismProperty.IsStableUnderComposition
      (@IsClosedImmersion : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@IsClosedImmersion : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  change IsClosedImmersion (pullback.map X.hom Y.hom X.hom Z.hom
    (𝟙 X.left) q.left (𝟙 _) (by simp) (by simp))
  exact MorphismProperty.pullbackMap (P := @AlgebraicGeometry.IsClosedImmersion)
    (inferInstance : IsClosedImmersion (𝟙 X.left))
    (inferInstance : IsClosedImmersion q.left) (by simp) (MorphismProperty.Over.w q).symm

/-- Actual graph postcomposition is native pushforward when the ambient map is finite.
Every signed coefficient and every residue degree is retained. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Coproducts/Binary.lean: toIntegralCycle_comp_graph_of_finite"
  "adaptation" "actual native finite-cycle pushforward, with all signed coefficients"]
theorem comp_graph_val_of_finite
    {X Y Z : Scheme.SmoothSite (Spec (.of k))} (q : Y ⟶ Z)
    [IsFinite (graphTargetMap k X q)] (α : Cor.mk X ⟶ Cor.mk Y) :
    (α ≫ (graphFunctor k).map q).val =
      finiteCyclePushforward (graphTargetMap k X q) α.val := by
  classical
  have heq :
      (finiteCorrespondences X.hom Z.hom).subtype.comp
          ((incidenceTorPairing X.hom Y.hom Z.hom).flip
            (graphCorrespondenceOfComponents Y.hom Z.hom q.left
              (MorphismProperty.Over.w q) (finite_genericPoints k (Cor.mk Y)))) =
        (finiteCyclePushforward (graphTargetMap k X q)).comp
          (finiteCorrespondences X.hom Y.hom).subtype := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro z hz
    change (incidenceTorPairing X.hom Y.hom Z.hom
      (singleFiniteCorrespondence X.hom Y.hom z hz 1)
      (graphCorrespondenceOfComponents Y.hom Z.hom q.left
        (MorphismProperty.Over.w q) (finite_genericPoints k (Cor.mk Y)))).val = _
    rw [incidenceTorPairing_single_graph_right_val]
    change finiteCyclePushforward
        ((integralComponentAt z).subschemeι ≫ graphTargetMap k X q)
        (single (genericPoint (integralComponentAt z).subscheme) 1) =
      finiteCyclePushforward (graphTargetMap k X q) (single z 1)
    have hz' : (integralComponentAt z).subschemeι
        (genericPoint (integralComponentAt z).subscheme) = z :=
      genericPointOf_integralComponentAt z
    rw [← finiteCyclePushforward_comp_apply,
      finiteCyclePushforward_single_of_isClosedImmersion, hz']
  exact DFunLike.congr_fun heq α

/-- The graph of an actual closed immersion is mono in the native correspondence category. -/
instance graph_map_mono_of_isClosedImmersion
    {Y Z : Scheme.SmoothSite (Spec (.of k))} (q : Y ⟶ Z) [IsClosedImmersion q.left] :
    Mono ((graphFunctor k).map q) where
  right_cancellation {X} α β h := by
    apply Subtype.ext
    apply finiteCyclePushforward_injective_of_isClosedImmersion
      (graphTargetMap k X.toSmoothSite q)
    have h' := congrArg
      (fun c : finiteCorrespondences X.toSmoothSite.hom Z.hom => c.val) h
    exact (comp_graph_val_of_finite k q α).symm.trans
      (h'.trans (comp_graph_val_of_finite k q β))

end AlgebraicGeometry.Cor

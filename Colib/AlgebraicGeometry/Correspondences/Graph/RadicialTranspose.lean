/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteInjectivePushforward
public import Colib.AlgebraicGeometry.Correspondences.Graph.Transpose

/-!
# Both actual graph-transpose degree identities for finite flat radicial maps

The graph of a finite universally injective morphism is mono in the native correspondence
category: graph postcomposition is the original finite cycle pushforward, whose point map is
injective and whose full residue degrees are nonzero. This applies to the product map for
every original smooth source, including empty and disconnected sources.

For integral smooth objects, cancel this graph from the already proved transpose-then-graph
degree equation to obtain the opposite actual incidence Tor composite. All multiplicities of
that composite are retained. The proof never replaces the self-fiber product by its reduction
or claims that its two projections agree as scheme morphisms. Only equality of the original
cycles is concluded. No field-change or perfection equivalence is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {X Y : Scheme.SmoothSite (Spec (.of k))} (q : X ⟶ Y)

instance graphTargetMap_isFinite [IsFinite q.left]
    (T : Scheme.SmoothSite (Spec (.of k))) : IsFinite (graphTargetMap k T q) := by
  change IsFinite (pullback.map T.hom X.hom T.hom Y.hom
    (𝟙 T.left) q.left (𝟙 _) (by simp) (by simp))
  exact MorphismProperty.pullbackMap (P := @AlgebraicGeometry.IsFinite)
    (inferInstance : IsFinite (𝟙 T.left)) (inferInstance : IsFinite q.left)
    (by simp) (MorphismProperty.Over.w q).symm

instance graphTargetMap_universallyInjective [UniversallyInjective q.left]
    (T : Scheme.SmoothSite (Spec (.of k))) :
    UniversallyInjective (graphTargetMap k T q) := by
  change UniversallyInjective (pullback.map T.hom X.hom T.hom Y.hom
    (𝟙 T.left) q.left (𝟙 _) (by simp) (by simp))
  exact MorphismProperty.pullbackMap (P := @AlgebraicGeometry.UniversallyInjective)
    (inferInstance : UniversallyInjective (𝟙 T.left))
    (inferInstance : UniversallyInjective q.left)
    (by simp) (MorphismProperty.Over.w q).symm

/-- The original graph of a finite radicial map is mono for actual finite correspondences.
Cancellation uses all integral cycle coefficients and full nonzero residue-degree weights. -/
@[colib_tag "COL-1091", stacks 01S4 "radicial maps remain injective after product base change",
  stacks 02R4 "actual finite cycle pushforward has nonzero residue-degree weights"]
instance graph_map_mono_of_finite_universallyInjective
    [IsFinite q.left] [UniversallyInjective q.left] : Mono ((graphFunctor k).map q) where
  right_cancellation {T} α β h := by
    apply Subtype.ext
    apply finiteCyclePushforward_injective_of_injective
      (graphTargetMap k T.toSmoothSite q) (graphTargetMap k T.toSmoothSite q).injective
    have h' := congrArg
      (fun c : finiteCorrespondences T.toSmoothSite.hom Y.hom => c.val) h
    exact (comp_graph_val_of_finite k q α).symm.trans
      (h'.trans (comp_graph_val_of_finite k q β))

/-- For a finite flat radicial map of integral smooth objects, the opposite actual Tor
composite is the full generic degree times the original source identity. -/
@[colib_tag "COL-1091", colib_ref "MVW2006"
  "Lecture 1, transpose and composition, printed pp. 4-5; Exercise 1.11, printed p. 6"
  "adaptation" "both native graph-transpose degree identities, using radicial graph cancellation"]
theorem graph_comp_finiteFlatTranspose_of_universallyInjective
    [IsIntegral X.left] [IsIntegral Y.left] [IsFinite q.left] [Flat q.left]
    [UniversallyInjective q.left] :
    (graphFunctor k).map q ≫ finiteFlatTranspose k q =
      (q.left.residueDegree (genericPoint X.left) : ℤ) • 𝟙 (Cor.mk X) := by
  let γ : Cor.mk X ⟶ Cor.mk Y := (graphFunctor k).map q
  let τ : Cor.mk Y ⟶ Cor.mk X := finiteFlatTranspose k q
  let d : ℤ := q.left.residueDegree (genericPoint X.left)
  have : Mono γ := graph_map_mono_of_finite_universallyInjective k q
  have hdegree : τ ≫ γ = d • 𝟙 (Cor.mk Y) :=
    finiteFlatTranspose_comp_graph_of_isIntegral k q
  apply (cancel_mono γ).mp
  change (γ ≫ τ) ≫ γ = (d • 𝟙 (Cor.mk X)) ≫ γ
  calc
    (γ ≫ τ) ≫ γ = γ ≫ (τ ≫ γ) := Category.assoc _ _ _
    _ = γ ≫ (d • 𝟙 (Cor.mk Y)) := congrArg (fun c : Cor.mk Y ⟶ Cor.mk Y => γ ≫ c) hdegree
    _ = d • γ := by rw [Preadditive.comp_zsmul, Category.comp_id]
    _ = (d • 𝟙 (Cor.mk X)) ≫ γ := by rw [Preadditive.zsmul_comp, Category.id_comp]

end AlgebraicGeometry.Cor

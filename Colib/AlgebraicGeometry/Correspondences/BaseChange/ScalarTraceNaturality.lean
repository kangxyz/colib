/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.ScalarTrace
public import Colib.AlgebraicGeometry.Correspondences.Graph.WholeFiniteFlatPullback
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Isomorphism

/-!
# Cartesian naturality of the actual whole finite-flat trace

The trace is the existing whole finite-flat span. Its paired support is closed
because its second projection is the identity. Native flat graph precomposition
and an isomorphism preserving both original legs identify the entire pullback
span, with no reduction or componentwise flatness premise.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/BaseChange/ScalarTrace.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, blob
`689f9e6bac02314fe9a3e8caee212e703ef172ec`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- Flat Cartesian restriction commutes with the existing whole-support trace. -/
theorem finiteFlatTrace_cartesian {X Y U V : SmoothSite (Spec (.of k))}
    (p : Y ⟶ X) [IsFinite p.left] [Flat p.left]
    (q : V ⟶ U) [IsFinite q.left] [Flat q.left]
    (j : U ⟶ X) [Flat j.left] (i : V ⟶ Y)
    (sq : IsPullback q.left i.left j.left p.left) :
    finiteFlatTrace q ≫ (graphFunctor k).map i =
      (graphFunctor k).map j ≫ finiteFlatTrace p := by
  let h : p.left ≫ X.hom = (𝟙 Y.left) ≫ Y.hom := by
    simp only [Category.id_comp, MorphismProperty.Over.w]
  let m : Y.left ⟶ pullback X.hom Y.hom := pullback.lift p.left (𝟙 Y.left) h
  let : IsClosedImmersion m := by
    have : IsClosedImmersion (m ≫ pullback.snd X.hom Y.hom) := by
      simpa only [m, pullback.lift_snd] using
        (inferInstance : IsClosedImmersion (𝟙 Y.left))
    exact IsClosedImmersion.of_comp m (pullback.snd X.hom Y.hom)
  change ofFiniteFlatSpan q.left (𝟙 V.left) _ ≫ (graphFunctor k).map i =
    (graphFunctor k).map j ≫ ofFiniteFlatSpan p.left (𝟙 Y.left) h
  rw [ofFiniteFlatSpan_comp_graph,
    graph_comp_ofFiniteFlatSpan_of_flat j p.left (𝟙 Y.left) h]
  simp only [Category.id_comp, Category.comp_id]
  exact ofFiniteFlatSpan_eq_of_iso sq.isoPullback q.left i.left _
    (pullback.fst j.left p.left) (pullback.snd j.left p.left) _
    sq.isoPullback_hom_fst sq.isoPullback_hom_snd

variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- The scalar trace is natural for each flat original map, with the actual scalar map. -/
theorem finiteScalarTrace_naturality {U X : SmoothSite (Spec (.of k))}
    (j : U ⟶ X) [Flat j.left] :
    finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) U) ≫
        (graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) j) =
      (graphFunctor k).map j ≫
        finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X) :=
  finiteFlatTrace_cartesian _ _ j _ (SmoothSite.finiteScalarMap_isPullback j)

end AlgebraicGeometry.Cor

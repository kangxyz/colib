/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.ClosedFlatCycle
public import Colib.AlgebraicGeometry.Correspondences.Graph.WholeFiniteFlatEndpoint

/-!
# Flat graph precomposition of a genuine whole finite-flat span

This API is sufficient for the original smooth alpha and flat beta maps. It
requires that the actual paired support map be closed, as supplied by the
retained-product producer. It does not assert that an arbitrary finite span
is closed and does not assume that individual source components are flat.
All pullbacks are whole scheme-theoretic pullbacks, with their original maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

open Stacks.Chow Scheme

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))} {D : Scheme.{u}}
  (φ : X ⟶ Y) [Flat φ.left]

/-- A flat left graph pulls the actual whole closed finite-flat span back. -/
theorem graph_comp_ofFiniteFlatSpan_pair_of_flat
    (m : D ⟶ pullback Y.hom Z.hom) [IsClosedImmersion m]
    [IsFinite (m ≫ pullback.fst Y.hom Z.hom)] [Flat (m ≫ pullback.fst Y.hom Z.hom)] :
    (graphFunctor k).map φ ≫
      ofFiniteFlatSpan (m ≫ pullback.fst Y.hom Z.hom) (m ≫ pullback.snd Y.hom Z.hom)
        (by simp only [Category.assoc, pullback.condition]) =
      ofFiniteFlatSpan (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
        (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom) ≫
          m ≫ pullback.snd Y.hom Z.hom) (wholeEndpoint_base φ m) := by
  haveI := isNoetherian_of_finiteType (m ≫ pullback.fst Y.hom Z.hom)
  haveI := isNoetherian_of_finiteType
    (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
  rw [ofFiniteFlatSpan_pair]
  apply Subtype.ext
  rw [graph_comp_closedFiniteFlatSpan_val_eq_whole_flat_pullback φ m,
    ofFiniteFlatSpan_val]
  rfl

/-- The source and target of the whole pullback span retain the original base equation. -/
theorem flatWholeSpan_base (p : D ⟶ Y.left) (g : D ⟶ Z.left)
    (hp : p ≫ Y.hom = g ≫ Z.hom) :
    pullback.fst φ.left p ≫ X.hom = (pullback.snd φ.left p ≫ g) ≫ Z.hom := by
  rw [← MorphismProperty.Over.w φ, ← Category.assoc, pullback.condition]
  simp only [Category.assoc, hp]

/-- Direct source-and-target API for alpha and beta: the closedness hypothesis
is exactly the paired map supplied by the retained-product construction. -/
theorem graph_comp_ofFiniteFlatSpan_of_flat
    (p : D ⟶ Y.left) (g : D ⟶ Z.left) (hp : p ≫ Y.hom = g ≫ Z.hom)
    [IsFinite p] [Flat p] [IsClosedImmersion (pullback.lift p g hp)] :
    (graphFunctor k).map φ ≫ ofFiniteFlatSpan p g hp =
      ofFiniteFlatSpan (pullback.fst φ.left p) (pullback.snd φ.left p ≫ g)
        (flatWholeSpan_base φ p g hp) := by
  let m := pullback.lift p g hp
  haveI : IsFinite (m ≫ pullback.fst Y.hom Z.hom) := by
    simpa only [m, pullback.lift_fst] using (inferInstance : IsFinite p)
  haveI : Flat (m ≫ pullback.fst Y.hom Z.hom) := by
    simpa only [m, pullback.lift_fst] using (inferInstance : Flat p)
  simpa only [m, pullback.lift_fst, pullback.lift_snd, Category.assoc] using
    graph_comp_ofFiniteFlatSpan_pair_of_flat φ m

end AlgebraicGeometry.Cor

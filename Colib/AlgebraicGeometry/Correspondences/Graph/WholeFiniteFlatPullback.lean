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

open Stacks.Chow _root_.AlgebraicGeometry.Scheme

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
  let : IsNoetherian ((𝟭 Scheme).obj Y.left) := inferInstanceAs (IsNoetherian Y.left)
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  have := isNoetherian_of_finiteType_of_isNoetherian (m ≫ pullback.fst Y.hom Z.hom)
  have := isNoetherian_of_finiteType_of_isNoetherian
    (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
  rw [ofFiniteFlatSpan_pair]
  apply Subtype.ext
  rw [graph_comp_closedFiniteFlatSpan_val_eq_whole_flat_pullback φ m,
    ofFiniteFlatSpan_val]
  rfl

omit [Flat φ.left] in
/-- The source and target of the whole pullback span retain the original base equation. -/
theorem flatWholeSpan_base (p : D ⟶ Y.left) (g : D ⟶ Z.left)
    (hp : p ≫ Y.hom = g ≫ Z.hom) :
    pullback.fst φ.left p ≫ X.hom = (pullback.snd φ.left p ≫ g) ≫ Z.hom := by
  rw [← MorphismProperty.Over.w φ, ← Category.assoc, pullback.condition]
  simp only [Category.assoc, hp]

omit [Flat φ.left] in
private theorem graph_comp_span_transport
    (p₀ p₁ : D ⟶ Y.left) [IsFinite p₀] [Flat p₀] [IsFinite p₁] [Flat p₁]
    (g₀ g₁ : D ⟶ Z.left) (h₀ : p₀ ≫ Y.hom = g₀ ≫ Z.hom)
    (h₁ : p₁ ≫ Y.hom = g₁ ≫ Z.hom) (hp : p₀ = p₁) (hg : g₀ = g₁)
    (h : (graphFunctor k).map φ ≫ ofFiniteFlatSpan (X := Y) (Y := Z) p₀ g₀ h₀ =
      ofFiniteFlatSpan (X := X) (Y := Z) (pullback.fst φ.left p₀) (pullback.snd φ.left p₀ ≫ g₀)
        (flatWholeSpan_base φ p₀ g₀ h₀)) :
    (graphFunctor k).map φ ≫ ofFiniteFlatSpan (X := Y) (Y := Z) p₁ g₁ h₁ =
      ofFiniteFlatSpan (X := X) (Y := Z) (pullback.fst φ.left p₁) (pullback.snd φ.left p₁ ≫ g₁)
        (flatWholeSpan_base φ p₁ g₁ h₁) := by
  subst p₁
  subst g₁
  exact h

/-- Direct source-and-target API for alpha and beta: the closedness hypothesis
is exactly the paired map supplied by the retained-product construction. -/
theorem graph_comp_ofFiniteFlatSpan_of_flat
    (p : D ⟶ Y.left) (g : D ⟶ Z.left) (hp : p ≫ Y.hom = g ≫ Z.hom)
    [IsFinite p] [Flat p] [IsClosedImmersion (pullback.lift p g hp)] :
    (graphFunctor k).map φ ≫ ofFiniteFlatSpan p g hp =
      ofFiniteFlatSpan (pullback.fst φ.left p) (pullback.snd φ.left p ≫ g)
        (flatWholeSpan_base φ p g hp) := by
  let m := pullback.lift p g hp
  have : IsFinite (m ≫ pullback.fst Y.hom Z.hom) := by
    simpa only [m, pullback.lift_fst] using (inferInstance : IsFinite p)
  have : Flat (m ≫ pullback.fst Y.hom Z.hom) := by
    simpa only [m, pullback.lift_fst] using (inferInstance : Flat p)
  let p' := m ≫ pullback.fst Y.hom Z.hom
  let g' := m ≫ pullback.snd Y.hom Z.hom
  have hbase : p' ≫ Y.hom = g' ≫ Z.hom := by
    simp only [p', g', Category.assoc, pullback.condition]
  exact graph_comp_span_transport φ p' p g' g hbase hp
    (pullback.lift_fst p g hp) (pullback.lift_snd p g hp)
    (graph_comp_ofFiniteFlatSpan_pair_of_flat φ m)

end AlgebraicGeometry.Cor

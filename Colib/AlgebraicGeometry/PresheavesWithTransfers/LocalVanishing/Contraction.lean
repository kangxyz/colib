/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Contraction
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.AffineLocalization

/-!
# Generic open zeros of the original contraction

A localization zero of a Laurent-cylinder representative gives a localization
zero of the corresponding class under the actual contraction quotient.

Adapted from `Motivic/Cohomology/Sheaf/TorusModelGerm.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `0f3ccc41d7720cbf70d024830d74352ef6c74c4d`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.Algebra.Smooth

attribute [local instance] away_smooth

variable {k : Type u} [Field k]

/-- Localization zero descends through the literal quotient of torus sections. -/
theorem contraction_affineLocalizationZero
    (P : PresheafWithTransfers.{v} k) (h : (torusSections P).AffineLocalizationZero) :
    (contraction P).AffineLocalizationZero := by
  intro R _ _ _ _ s
  obtain ⟨t, rfl⟩ := toContraction_surjective P (Cor.mk (affineSite k R)) s
  obtain ⟨r, hr, hz⟩ := h R t
  refine ⟨r, hr, ?_⟩
  let f := affineMorphism (IsScalarTower.toAlgHom k R (Localization.Away r))
  let T := multiplicativeGroupObject (Spec (.of k))
  have hz' : transfer P ((Cor.parameterProduct T).map ((Cor.graphFunctor k).map f)) t = 0 := hz
  rw [Cor.parameterProduct_graph] at hz'
  change transfer (contraction P) ((Cor.graphFunctor k).map f)
    ((toContraction P).hom.app (op (Cor.mk (affineSite k R))) t) = 0
  rw [contraction_graph_apply]
  exact (congrArg ((toContraction P).hom.app
    (op (Cor.mk (affineSite k (Localization.Away r))))) hz').trans (map_zero _)

end AlgebraicGeometry.PresheafWithTransfers

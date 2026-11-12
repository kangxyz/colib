/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.ConnectorSimplexFaces
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Coherence under every increasing simplex face

Any non-surjective mono factors through an elementary coface. Induction on
the target dimension therefore upgrades the constructed elementary face
identities to every mono. This is the coherence needed by the nondegenerate
simplex colimit; no identity for unaggregated repeated vertices is claimed.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/Realization/ConnectorMonoCoherence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity CategoryTheory
open scoped Topology unitInterval Simplicial
universe u
namespace Topology.NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A] (E : LocalEquiconnection A)

/-- Ordered connector interpolation commutes with every injective simplex operator. -/
theorem interpolate_mono : ∀ (m : ℕ) {n : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) [Mono φ]
    (v : Fin (m + 1) → A) (hv : AdmissibleVertices E v)
    (x : StdSimplex ℝ (Fin (n + 1))),
    interpolate E v hv (x.map φ.toOrderHom) =
      interpolate E (v ∘ φ.toOrderHom) (hv.comp φ.toOrderHom) x := by
  intro m
  induction m with
  | zero =>
    intro n φ hφ v hv x
    have hn : n ≤ 0 := SimplexCategory.len_le_of_mono φ
    have hnzero : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    rw [SimplexCategory.eq_id_of_mono φ]
    change interpolate E v hv (x.map id) = interpolate E (v ∘ id) _ x
    simp only [StdSimplex.map_id, Function.comp_id]
  | succ m ih =>
    intro n φ hφ v hv x
    by_cases hs : Function.Surjective φ.toOrderHom
    · have : Epi φ := (SimplexCategory.epi_iff_surjective (f := φ)).mpr hs
      have hn : n = m + 1 := le_antisymm (SimplexCategory.len_le_of_mono φ)
        (SimplexCategory.len_le_of_epi φ)
      subst n
      rw [SimplexCategory.eq_id_of_mono φ]
      change interpolate E v hv (x.map id) = interpolate E (v ∘ id) _ x
      simp only [StdSimplex.map_id, Function.comp_id]
    · obtain ⟨i, ψ, hψ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective φ hs
      have : Mono (ψ ≫ SimplexCategory.δ i) := by rw [← hψ]; infer_instance
      have : Mono ψ := mono_of_mono ψ (SimplexCategory.δ i)
      rw [hψ]
      change interpolate E v hv (x.map (i.succAbove ∘ ψ.toOrderHom)) =
        interpolate E (v ∘ (i.succAbove ∘ ψ.toOrderHom)) _ x
      rw [StdSimplex.map_comp, interpolate_face]
      exact ih ψ (v ∘ i.succAbove) (hv.comp i.succAbove) x

/-- Every simplex vertex has exactly its selected target value. -/
theorem interpolate_vertex {n : ℕ} (v : Fin (n + 1) → A)
    (hv : AdmissibleVertices E v) (i : Fin (n + 1)) :
    interpolate E v hv (StdSimplex.single i) = v i := by
  let φ : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const _ _ i
  have : Mono φ := (SimplexCategory.mono_iff_injective (f := φ)).mpr
    (by
      intro a b _
      change Fin 1 at a b
      exact Subsingleton.elim a b)
  have h := interpolate_mono E n φ v hv (StdSimplex.single 0)
  simpa [φ, StdSimplex.map_single, interpolate_zero, SimplexCategory.const] using h

end Topology.NumerableConnectorCover

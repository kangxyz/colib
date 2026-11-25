/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Colib.KTheory.Waldhausen.Iterated.SimplexParameterPaths

/-!
# Embedding scalar paths in larger simplices

Adapted from `Quillen/Waldhausen/SConstruction/Iterated/SimplexPathEmbedding.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Topology
open scoped Simplicial Topology unitInterval
universe u v
namespace Path.Homotopy

/-- The path homotopy obtained by composing `J` with `φ`, with its boundary paths identified with
`p′` and `q′` by the supplied pointwise equalities.
-/
def mapOfPaths {Z : Type u} {Z' : Type v} [TopologicalSpace Z] [TopologicalSpace Z']
    {a b : Z} {a' b' : Z'} {p q : Path a b} (φ : C(Z, Z')) (J : p.Homotopy q)
    (p' q' : Path a' b') (hp : ∀ t, φ (p t) = p' t) (hq : ∀ t, φ (q t) = q' t) :
    p'.Homotopy q' where
  toFun z := φ (J z)
  continuous_toFun := φ.continuous.comp J.continuous
  map_zero_left t := (congrArg φ (J.apply_zero t)).trans (hp t)
  map_one_left t := (congrArg φ (J.apply_one t)).trans (hq t)
  prop' r t ht := by
    change φ (J (r, t)) = p' t
    rw [J.eq_fst r ht]
    exact hp t
end Path.Homotopy

namespace CategoryTheory.Waldhausen.IteratedS.SimplexParameters

theorem map_trans_values {Z : Type u} {Z' : Type v} [TopologicalSpace Z]
    [TopologicalSpace Z'] {a b c : Z} {a' b' c' : Z'} (φ : Z → Z')
    (p : Path a b) (q : Path b c) (p' : Path a' b') (q' : Path b' c')
    (hp : ∀ t, φ (p t) = p' t) (hq : ∀ t, φ (q t) = q' t) (t : unitInterval) :
    φ ((p.trans q) t) = (p'.trans q') t := by
  rw [Path.trans_apply, Path.trans_apply]
  split
  · exact hp _
  · exact hq _

/-- The continuous map of geometric simplices induced by the simplex morphism `α`. -/
def embed {k l : ℕ} (α : ⦋l⦌ ⟶ ⦋k⦌) :
    C(StdSimplex ℝ (Fin (l + 1)), StdSimplex ℝ (Fin (k + 1))) :=
  ⟨StdSimplex.map α.toOrderHom, by fun_prop⟩

/-- The path from vertex `i` to vertex `m` obtained by concatenating the edges through vertex `j`.
-/
def binaryPath {k : ℕ} (i j m : Fin (k + 1)) :
    Path (StdSimplex.single i : StdSimplex ℝ (Fin (k + 1))) (StdSimplex.single m) :=
  (edge i j).trans (edge j m)

theorem map_edge {k l : ℕ} (α : ⦋l⦌ ⟶ ⦋k⦌) (i j : Fin (l + 1)) (t : unitInterval) :
    embed α (edge i j t) = edge (α.toOrderHom i) (α.toOrderHom j) t :=
  StdSimplex.map_duple (unitInterval.nonneg (unitInterval.symm t))
    (unitInterval.nonneg t) (by simp) i j α.toOrderHom

theorem map_binaryPath {k l : ℕ} (α : ⦋l⦌ ⟶ ⦋k⦌)
    (i j m : Fin (l + 1)) (t : unitInterval) :
    embed α (binaryPath i j m t) =
      binaryPath (α.toOrderHom i) (α.toOrderHom j) (α.toOrderHom m) t :=
  map_trans_values _ _ _ _ _ (map_edge α i j) (map_edge α j m) t

end CategoryTheory.Waldhausen.IteratedS.SimplexParameters

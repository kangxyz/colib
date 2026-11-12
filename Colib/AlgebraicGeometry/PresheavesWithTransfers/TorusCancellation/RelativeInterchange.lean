/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.InterchangeHomotopy
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.SimplexFaceGeometry

/-!
# The chosen torus interchange relative to all original simplex faces

Each original coface is a Cartesian polynomial endpoint. The retained
quadratic family and the signed gluing both commute with that restriction.
Consequently the chosen homotopy vanishes on every face on which the
original correspondence vanishes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction
open scoped Simplicial

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "F" => Cor.parameterProduct (multiplicativeGroupObject Sₖ)
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)
local notation "Δ(" n ")" => AlgebraicSimplex.smoothSiteObj k n
set_option quotPrecheck false in
local notation "face(" U "," i ")" =>
  SmoothSite.productMap (𝟙 U) ((AlgebraicSimplex.cosimplicialSmoothSite k).δ i)

/-- The chosen swap homotopy commutes with the original coface on the smooth source. -/
theorem torusDoubleSwapHomotopy_simplex_face
    (U : SmoothSite (Spec (CommRingCat.of k))) {n : ℕ} (i : Fin (n + 2)) :
    γ (affineLineCylinder.map (torusDoubleBaseMap k (face(U,i)))) ≫
        torusDoubleSwapHomotopy k (Cor.mk (product U (Δ(n + 1)))) =
      torusDoubleSwapHomotopy k (Cor.mk (product U (Δ(n)))) ≫
        γ (torusDoubleBaseMap k (face(U,i))) := by
  obtain ⟨q, hq, H⟩ := AlgebraicSimplex.product_coface_cartesian_polynomial k i U
  let : Flat q := hq
  exact torusDoubleSwapHomotopy_graph_precomp_of_cartesian_face k
    (Cor.mk (product U (Δ(n + 1)))) (face(U,i)) q 0 H

/-- Restriction of the chosen interchange is the interchange of the original
restriction by the literal coface. -/
theorem torusReducedExtensionsHomotopy_simplex_face
    (U : SmoothSite (Spec (CommRingCat.of k))) {n : ℕ} (i : Fin (n + 2)) {Y : Cor k}
    (α : (F).obj (Cor.mk (product U (Δ(n + 1)))) ⟶ (F).obj Y) :
    γ (affineLineCylinder.map (torusDoubleBaseMap k (face(U,i)))) ≫
        torusReducedExtensionsHomotopy k α =
      torusReducedExtensionsHomotopy k ((F).map (γ (face(U,i))) ≫ α) :=
  torusReducedExtensionsHomotopy_graph_precomp k (face(U,i)) α
    (torusDoubleSwapHomotopy_simplex_face k U i)

/-- The chosen interchange vanishes on a face where the original correspondence vanishes. -/
theorem torusReducedExtensionsHomotopy_simplex_face_eq_zero
    (U : SmoothSite (Spec (CommRingCat.of k))) {n : ℕ} (i : Fin (n + 2)) {Y : Cor k}
    (α : (F).obj (Cor.mk (product U (Δ(n + 1)))) ⟶ (F).obj Y)
    (hα : (F).map (γ (face(U,i))) ≫ α = 0) :
    γ (affineLineCylinder.map (torusDoubleBaseMap k (face(U,i)))) ≫
        torusReducedExtensionsHomotopy k α = 0 := by
  rw [torusReducedExtensionsHomotopy_simplex_face k U i α, hα,
    torusReducedExtensionsHomotopy_zero]

end AlgebraicGeometry.PresheafWithTransfers

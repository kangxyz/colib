/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Parameter
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineSectionNaturality

/-!
# Reordering the affine and torus parameters in correspondences

The original product permutation places the torus in the position used by
the signed power cut. It carries the original affine sections and commutes
with graphs of base maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "A₁" => additiveGroupObject Sₖ
local notation "Gₘ" => multiplicativeGroupObject Sₖ
local notation "C" => Cor.parameterProduct A₁
local notation "F" => Cor.parameterProduct Gₘ
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)

/-- The graph of the original factor permutation from affine then torus
to torus then affine. -/
abbrev torusAffineSwap (X : Cor k) :
    (F).obj ((C).obj X) ⟶ (C).obj ((F).obj X) :=
  γ (productSwapLast X.toSmoothSite A₁ Gₘ)

/-- The actual scalar sections are transported by the graph of the permutation. -/
@[reassoc]
theorem torusAffineSwap_section (X : Cor k) (a : k) :
    (F).map (γ (nativeAffineSection (.of k) X.toSmoothSite a)) ≫ torusAffineSwap k X =
      γ (nativeAffineSection (.of k) ((F).obj X).toSmoothSite a) := by
  rw [Cor.parameterProduct_graph]
  let U := X.toSmoothSite
  let s : U ⟶ SmoothSite.product U A₁ := nativeAffineSection (.of k) U a
  let t : SmoothSite.product U Gₘ ⟶ SmoothSite.product (SmoothSite.product U Gₘ) A₁ :=
    nativeAffineSection (.of k) (SmoothSite.product U Gₘ) a
  let v := SmoothSite.productMap s (𝟙 Gₘ)
  let p := productSwapLast U A₁ Gₘ
  change γ v ≫ γ p = γ t
  have h : v ≫ p = t := productMap_nativeAffineSection_comp_productSwapLast (.of k) U Gₘ a
  exact ((Cor.graphFunctor k).map_comp v p).symm.trans
    (congrArg (fun f : SmoothSite.product U Gₘ ⟶ _ => γ f) h)

/-- Reordering the two parameters commutes with every original base graph. -/
@[reassoc]
theorem torusAffineSwap_graph_naturality {X Y : Cor k} (f : X.toSmoothSite ⟶ Y.toSmoothSite) :
    (F).map (γ (affineLineCylinder.map f)) ≫ torusAffineSwap k Y =
      torusAffineSwap k X ≫ γ (affineLineCylinder.map (SmoothSite.productMap f (𝟙 Gₘ))) := by
  rw [Cor.parameterProduct_graph]
  change γ (SmoothSite.productMap (SmoothSite.productMap f (𝟙 A₁)) (𝟙 Gₘ)) ≫
    γ (productSwapLast Y.toSmoothSite A₁ Gₘ) =
    γ (productSwapLast X.toSmoothSite A₁ Gₘ) ≫
      γ (SmoothSite.productMap (SmoothSite.productMap f (𝟙 Gₘ)) (𝟙 A₁))
  simp only [← Functor.map_comp, productSwapLast_naturality]

end AlgebraicGeometry.PresheafWithTransfers

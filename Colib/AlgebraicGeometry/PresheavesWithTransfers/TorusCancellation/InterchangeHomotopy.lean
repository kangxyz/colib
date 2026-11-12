/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Interchange
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.RetainedSwap

/-!
# The interchange of the two reduced torus extensions

The swap homotopy over each original smooth base supplies the endpoints
needed for Voevodsky's Lemma 4.7. The two extensions are the actual signed
correspondences in the native right-factor product coordinates.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "F" => Cor.parameterProduct (multiplicativeGroupObject Sₖ)
local notation "C" => Cor.parameterProduct (additiveGroupObject Sₖ)
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)
set_option quotPrecheck false in
local notation "D(" X ")" => ((F).obj ((F).obj X))
set_option quotPrecheck false in
local notation "σ(" X "," a ")" => γ (nativeAffineSection (CommRingCat.of k) (X).toSmoothSite a)

/-- The chosen homotopy of the two actual reduced extensions. -/
abbrev torusReducedExtensionsHomotopy {X Y : Cor k} (α : (F).obj X ⟶ (F).obj Y) :
    (C).obj (D(X)) ⟶ D(Y) :=
  torusReducedInterchangeHomotopy k (torusDoubleSwapHomotopy k X)
    (torusDoubleSwapHomotopy k Y) α

@[simp]
theorem torusReducedExtensionsHomotopy_zero {X Y : Cor k} :
    torusReducedExtensionsHomotopy k (0 : (F).obj X ⟶ (F).obj Y) = 0 :=
  torusReducedInterchangeHomotopy_zero k _ _

/-- The chosen interchange has the original reduced extensions at the two affine endpoints. -/
theorem torusReducedExtensionsHomotopy_endpoints {X Y : Cor k}
    (α : (F).obj X ⟶ (F).obj Y)
    (hα : (𝟙 _ - torusUnitProjector k X) ≫ α ≫ (𝟙 _ - torusUnitProjector k Y) = α) :
    σ(D(X),0) ≫ torusReducedExtensionsHomotopy k α = torusInnerReducedExtension k α ∧
      σ(D(X),1) ≫ torusReducedExtensionsHomotopy k α = torusOuterReducedExtension k α :=
  torusReducedInterchangeHomotopy_endpoints_of_projectors k _ _ α hα
    (torusDoubleSwapHomotopy_endpoints k X) (torusDoubleSwapHomotopy_endpoints k Y)

/-- Restriction by a base graph preserves the chosen interchange whenever it
preserves the original swap homotopy. -/
theorem torusReducedExtensionsHomotopy_graph_precomp {X' X Y : Cor k}
    (f : X'.toSmoothSite ⟶ X.toSmoothSite) (α : (F).obj X ⟶ (F).obj Y)
    (hf : γ (affineLineCylinder.map (torusDoubleBaseMap k f)) ≫ torusDoubleSwapHomotopy k X =
      torusDoubleSwapHomotopy k X' ≫ γ (torusDoubleBaseMap k f)) :
    γ (affineLineCylinder.map (torusDoubleBaseMap k f)) ≫ torusReducedExtensionsHomotopy k α =
      torusReducedExtensionsHomotopy k ((F).map (γ f) ≫ α) :=
  torusReducedInterchangeHomotopy_graph_precomp k f _ _ _ α hf

/-- A compatible base graph on which the original signed correspondence
vanishes also kills the entire chosen homotopy. -/
theorem torusReducedExtensionsHomotopy_graph_precomp_eq_zero {X' X Y : Cor k}
    (f : X'.toSmoothSite ⟶ X.toSmoothSite) (α : (F).obj X ⟶ (F).obj Y)
    (hf : γ (affineLineCylinder.map (torusDoubleBaseMap k f)) ≫ torusDoubleSwapHomotopy k X =
      torusDoubleSwapHomotopy k X' ≫ γ (torusDoubleBaseMap k f))
    (hα : (F).map (γ f) ≫ α = 0) :
    γ (affineLineCylinder.map (torusDoubleBaseMap k f)) ≫ torusReducedExtensionsHomotopy k α =
      0 := by
  rw [torusReducedExtensionsHomotopy_graph_precomp k f α hf, hα,
    torusReducedExtensionsHomotopy_zero]

/-- The chosen interchange restricts to zero on a Cartesian polynomial face
where the original signed correspondence restricts to zero. -/
theorem torusReducedExtensionsHomotopy_cartesian_face_eq_zero {X' X Y : Cor k}
    (f : X'.toSmoothSite ⟶ X.toSmoothSite)
    (q : X.toSmoothSite.left ⟶ Spec (.of (Polynomial k))) [Flat q] (d : k)
    (H : IsPullback f.left X'.toSmoothSite.hom q (AffineLineFiber.point d))
    (α : (F).obj X ⟶ (F).obj Y) (hα : (F).map (γ f) ≫ α = 0) :
    γ (affineLineCylinder.map (torusDoubleBaseMap k f)) ≫ torusReducedExtensionsHomotopy k α =
      0 :=
  torusReducedExtensionsHomotopy_graph_precomp_eq_zero k f α
    (torusDoubleSwapHomotopy_graph_precomp_of_cartesian_face k X f q d H) hα

/-- The two extensions of a signed reduced correspondence are joined by an
actual finite correspondence on the native affine-line cylinder. -/
theorem exists_torusReducedExtensions_homotopy_of_reduced {X Y : Cor k}
    (α : (F).obj X ⟶ (F).obj Y)
    (hα : (𝟙 _ - torusUnitProjector k X) ≫ α ≫ (𝟙 _ - torusUnitProjector k Y) = α) :
    ∃ H : (C).obj (D(X)) ⟶ D(Y),
      σ(D(X),0) ≫ H = torusInnerReducedExtension k α ∧
      σ(D(X),1) ≫ H = torusOuterReducedExtension k α :=
  ⟨torusReducedExtensionsHomotopy k α, torusReducedExtensionsHomotopy_endpoints k α hα⟩

end AlgebraicGeometry.PresheafWithTransfers

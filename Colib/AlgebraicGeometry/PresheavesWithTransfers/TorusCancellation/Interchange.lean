/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.CylinderNaturality
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.DoubleTorus

/-!
# The interchange homotopy on actual signed reduced correspondences

A swap-to-inversion homotopy on each of the two original double torus
products is inserted on the source and target of the signed exterior
correspondence. The affine section naturality allows the two homotopies
to be added, subtracting their common endpoint. The outer inversions
cancel by their naturality on the actual signed correspondence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => multiplicativeGroupObject Sₖ
local notation "Aₖ" => additiveGroupObject Sₖ
local notation "F" => Cor.parameterProduct Gₖ
local notation "C" => Cor.parameterProduct Aₖ
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)
set_option quotPrecheck false in
local notation "D(" X ")" => ((F).obj ((F).obj X))
set_option quotPrecheck false in
local notation "σ(" X "," a ")" => γ (nativeAffineSection (CommRingCat.of k) (X).toSmoothSite a)

/-- The actual two-axis swap and outer inverse are joined on the original cylinder. -/
def HasTorusDoubleSwapHomotopy (X : Cor k) : Prop :=
  ∃ H : (C).obj (D(X)) ⟶ D(X),
    σ(D(X),0) ≫ H = torusDoubleSwap k X ≫ torusDoubleReduction k X ∧
    σ(D(X),1) ≫ H = torusDoubleInversion k X ≫ torusDoubleReduction k X

/-- The actual signed gluing of the source and target swap homotopies. -/
def torusReducedInterchangeHomotopy {X Y : Cor k}
    (HX : (C).obj (D(X)) ⟶ D(X)) (HY : (C).obj (D(Y)) ⟶ D(Y))
    (α : (F).obj X ⟶ (F).obj Y) : (C).obj (D(X)) ⟶ D(Y) :=
  let E := torusOuterReducedExtension k α
  let B := torusDoubleInversion k X ≫ E
  let p : (C).obj (D(X)) ⟶ D(X) :=
    γ ((SmoothSite.Contraction.projection Aₖ).app (D(X)).toSmoothSite)
  (HX ≫ E ≫ torusDoubleSwap k Y) + ((C).map B ≫ HY) - p ≫ B ≫ torusDoubleSwap k Y

/-- The signed gluing sends the zero correspondence to the zero homotopy. -/
@[simp]
theorem torusReducedInterchangeHomotopy_zero {X Y : Cor k}
    (HX : (C).obj (D(X)) ⟶ D(X)) (HY : (C).obj (D(Y)) ⟶ D(Y)) :
    torusReducedInterchangeHomotopy k HX HY 0 = 0 := by
  simp [torusReducedInterchangeHomotopy, torusOuterReducedExtension]

/-- The chosen gluing respects a base graph that commutes with the source swap homotopies. -/
theorem torusReducedInterchangeHomotopy_graph_precomp {X' X Y : Cor k}
    (f : X'.toSmoothSite ⟶ X.toSmoothSite)
    (HX' : (C).obj (D(X')) ⟶ D(X')) (HX : (C).obj (D(X)) ⟶ D(X))
    (HY : (C).obj (D(Y)) ⟶ D(Y)) (α : (F).obj X ⟶ (F).obj Y)
    (h : γ (affineLineCylinder.map (torusDoubleBaseMap k f)) ≫ HX =
      HX' ≫ γ (torusDoubleBaseMap k f)) :
    γ (affineLineCylinder.map (torusDoubleBaseMap k f)) ≫
        torusReducedInterchangeHomotopy k HX HY α =
      torusReducedInterchangeHomotopy k HX' HY ((F).map (γ f) ≫ α) := by
  let f₂ := torusDoubleBaseMap k f
  let a := γ (affineLineCylinder.map f₂)
  let b := γ f₂
  let α' := (F).map (γ f) ≫ α
  let E := torusOuterReducedExtension k α
  let E' := torusOuterReducedExtension k α'
  let B := torusDoubleInversion k X ≫ E
  let B' := torusDoubleInversion k X' ≫ E'
  let p : (C).obj (D(X)) ⟶ D(X) :=
    γ ((SmoothSite.Contraction.projection Aₖ).app (D(X)).toSmoothSite)
  let p' : (C).obj (D(X')) ⟶ D(X') :=
    γ ((SmoothSite.Contraction.projection Aₖ).app (D(X')).toSmoothSite)
  have hE : b ≫ E = E' := torusOuterReducedExtension_graph_precomp k f α
  have hI : b ≫ torusDoubleInversion k X = torusDoubleInversion k X' ≫ b :=
    torusDoubleInversion_baseMap k f
  have hB : b ≫ B = B' := by
    change b ≫ torusDoubleInversion k X ≫ E = torusDoubleInversion k X' ≫ E'
    rw [← Category.assoc, hI, Category.assoc, hE]
  have hC : (C).map b = a := Cor.parameterProduct_graph Aₖ f₂
  have hp : a ≫ p = p' ≫ b := by
    change γ (affineLineCylinder.map f₂) ≫ γ ((projection Aₖ).app (D(X)).toSmoothSite) =
      γ ((projection Aₖ).app (D(X')).toSmoothSite) ≫ γ f₂
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact (Cor.graphFunctor k).congr_map ((projection Aₖ).naturality f₂)
  have hL : a ≫ (HX ≫ E ≫ torusDoubleSwap k Y) = HX' ≫ E' ≫ torusDoubleSwap k Y := by
    rw [← Category.assoc, h, Category.assoc, ← Category.assoc b E, hE]
  have hR : a ≫ ((C).map B ≫ HY) = (C).map B' ≫ HY := by
    rw [← Category.assoc, ← hC, ← Functor.map_comp, hB]
  have hM : a ≫ (p ≫ B ≫ torusDoubleSwap k Y) = p' ≫ B' ≫ torusDoubleSwap k Y := by
    rw [← Category.assoc, hp, Category.assoc, ← Category.assoc b B, hB]
  change a ≫ ((HX ≫ E ≫ torusDoubleSwap k Y) + ((C).map B ≫ HY) - p ≫ B ≫
      torusDoubleSwap k Y) = (HX' ≫ E' ≫ torusDoubleSwap k Y) + ((C).map B' ≫ HY) -
      p' ≫ B' ≫ torusDoubleSwap k Y
  simp only [Preadditive.comp_sub, Preadditive.comp_add, hL, hR, hM]

/-- The two placements are the actual endpoints of the chosen signed gluing. -/
theorem torusReducedInterchangeHomotopy_endpoints {X Y : Cor k}
    (HX : (C).obj (D(X)) ⟶ D(X)) (HY : (C).obj (D(Y)) ⟶ D(Y))
    (α : (F).obj X ⟶ (F).obj Y)
    (hs : (𝟙 _ - torusUnitProjector k X) ≫ α = α)
    (ht : α ≫ (𝟙 _ - torusUnitProjector k Y) = α)
    (hX : σ(D(X),0) ≫ HX = torusDoubleSwap k X ≫ torusDoubleReduction k X ∧
      σ(D(X),1) ≫ HX = torusDoubleInversion k X ≫ torusDoubleReduction k X)
    (hY : σ(D(Y),0) ≫ HY = torusDoubleSwap k Y ≫ torusDoubleReduction k Y ∧
      σ(D(Y),1) ≫ HY = torusDoubleInversion k Y ≫ torusDoubleReduction k Y) :
    σ(D(X),0) ≫ torusReducedInterchangeHomotopy k HX HY α = torusInnerReducedExtension k α ∧
      σ(D(X),1) ≫ torusReducedInterchangeHomotopy k HX HY α =
        torusOuterReducedExtension k α := by
  obtain ⟨hX₀, hX₁⟩ := hX
  obtain ⟨hY₀, hY₁⟩ := hY
  let E := torusOuterReducedExtension k α
  let B := torusDoubleInversion k X ≫ E
  let M := B ≫ torusDoubleSwap k Y
  let p : (C).obj (D(X)) ⟶ D(X) :=
    γ ((SmoothSite.Contraction.projection Aₖ).app (D(X)).toSmoothSite)
  let L := HX ≫ E ≫ torusDoubleSwap k Y
  let R := (C).map B ≫ HY
  have hsrc : torusDoubleReduction k X ≫ E = E :=
    torusDoubleReduction_outerReducedExtension k α hs
  have htgt : E ≫ torusDoubleReduction k Y = E :=
    torusOuterReducedExtension_doubleReduction k α ht
  have hB : B ≫ torusDoubleReduction k Y = B := by
    change (torusDoubleInversion k X ≫ E) ≫ torusDoubleReduction k Y =
      torusDoubleInversion k X ≫ E
    rw [Category.assoc, htgt]
  have hp (a : k) : σ(D(X),a) ≫ p = 𝟙 (D(X)) := by
    change γ (nativeAffineSection (.of k) (D(X)).toSmoothSite a) ≫
      γ ((SmoothSite.Contraction.projection Aₖ).app (D(X)).toSmoothSite) = _
    rw [← Functor.map_comp, nativeAffineSection_projection, CategoryTheory.Functor.map_id]
    rfl
  have hconst (a : k) : σ(D(X),a) ≫ p ≫ M = M := by
    rw [← Category.assoc, hp]
    exact Category.id_comp M
  have hL₀ : σ(D(X),0) ≫ L = torusInnerReducedExtension k α := by
    change σ(D(X),0) ≫ HX ≫ E ≫ torusDoubleSwap k Y =
      torusDoubleSwap k X ≫ E ≫ torusDoubleSwap k Y
    rw [← Category.assoc, hX₀, Category.assoc,
      ← Category.assoc (torusDoubleReduction k X) E, hsrc]
  have hL₁ : σ(D(X),1) ≫ L = M := by
    change σ(D(X),1) ≫ HX ≫ E ≫ torusDoubleSwap k Y =
      (torusDoubleInversion k X ≫ E) ≫ torusDoubleSwap k Y
    rw [← Category.assoc, hX₁, Category.assoc,
      ← Category.assoc (torusDoubleReduction k X) E, hsrc,
      Category.assoc (torusDoubleInversion k X) E]
  have hR (a : k) : σ(D(X),a) ≫ R = B ≫ σ(D(Y),a) ≫ HY := by
    change σ(D(X),a) ≫ (C).map B ≫ HY = _
    rw [← Category.assoc, Cor.nativeAffineSection_graph_naturality, Category.assoc]
    rfl
  have hR₀ : σ(D(X),0) ≫ R = M := by
    change σ(D(X),0) ≫ R = B ≫ torusDoubleSwap k Y
    rw [hR, hY₀, torusDoubleSwap_reduction, ← Category.assoc, hB]
  have hR₁ : σ(D(X),1) ≫ R = E := by
    rw [hR, hY₁, ← Category.assoc]
    have hi : B ≫ torusDoubleInversion k Y = E :=
      (Category.assoc _ _ _).trans (torusDoubleInversion_conjugate k α)
    rw [hi, htgt]
  change σ(D(X),0) ≫ (L + R - p ≫ M) = torusInnerReducedExtension k α ∧
    σ(D(X),1) ≫ (L + R - p ≫ M) = E
  constructor
  · simp only [Preadditive.comp_sub, Preadditive.comp_add, hL₀, hR₀, hconst, add_sub_cancel_right]
  · simp only [Preadditive.comp_sub, Preadditive.comp_add, hL₁, hR₁, hconst, add_sub_cancel_left]

/-- The chosen gluing applies to the representatives selected by the original unit projectors. -/
theorem torusReducedInterchangeHomotopy_endpoints_of_projectors {X Y : Cor k}
    (HX : (C).obj (D(X)) ⟶ D(X)) (HY : (C).obj (D(Y)) ⟶ D(Y))
    (α : (F).obj X ⟶ (F).obj Y)
    (hα : (𝟙 _ - torusUnitProjector k X) ≫ α ≫ (𝟙 _ - torusUnitProjector k Y) = α)
    (hX : σ(D(X),0) ≫ HX = torusDoubleSwap k X ≫ torusDoubleReduction k X ∧
      σ(D(X),1) ≫ HX = torusDoubleInversion k X ≫ torusDoubleReduction k X)
    (hY : σ(D(Y),0) ≫ HY = torusDoubleSwap k Y ≫ torusDoubleReduction k Y ∧
      σ(D(Y),1) ≫ HY = torusDoubleInversion k Y ≫ torusDoubleReduction k Y) :
    σ(D(X),0) ≫ torusReducedInterchangeHomotopy k HX HY α = torusInnerReducedExtension k α ∧
      σ(D(X),1) ≫ torusReducedInterchangeHomotopy k HX HY α =
        torusOuterReducedExtension k α := by
  let p := 𝟙 _ - torusUnitProjector k X
  let q := 𝟙 _ - torusUnitProjector k Y
  have hp : p ≫ p = p := torusUnitComplement_idempotent k X
  have hq : q ≫ q = q := torusUnitComplement_idempotent k Y
  have h : p ≫ α ≫ q = α := hα
  have hs : p ≫ α = α := by
    calc
      _ = p ≫ p ≫ α ≫ q := congrArg (fun z => p ≫ z) h.symm
      _ = p ≫ α ≫ q := by rw [← Category.assoc, hp]
      _ = _ := h
  have ht : α ≫ q = α := by
    calc
      _ = (p ≫ α ≫ q) ≫ q := congrArg (fun z => z ≫ q) h.symm
      _ = p ≫ α ≫ q := by simp only [Category.assoc, hq]
      _ = _ := h
  exact torusReducedInterchangeHomotopy_endpoints k HX HY α hs ht hX hY

/-- The supplied swap homotopies give the native interchange homotopy. -/
theorem exists_torusReducedExtensions_homotopy_of_projectors {X Y : Cor k}
    (α : (F).obj X ⟶ (F).obj Y)
    (hα : (𝟙 _ - torusUnitProjector k X) ≫ α ≫ (𝟙 _ - torusUnitProjector k Y) = α)
    (hX : HasTorusDoubleSwapHomotopy k X) (hY : HasTorusDoubleSwapHomotopy k Y) :
    ∃ H : (C).obj (D(X)) ⟶ D(Y),
      σ(D(X),0) ≫ H = torusInnerReducedExtension k α ∧
      σ(D(X),1) ≫ H = torusOuterReducedExtension k α := by
  obtain ⟨HX, hX⟩ := hX
  obtain ⟨HY, hY⟩ := hY
  exact ⟨torusReducedInterchangeHomotopy k HX HY α,
    torusReducedInterchangeHomotopy_endpoints_of_projectors k HX HY α hα hX hY⟩

end AlgebraicGeometry.PresheafWithTransfers

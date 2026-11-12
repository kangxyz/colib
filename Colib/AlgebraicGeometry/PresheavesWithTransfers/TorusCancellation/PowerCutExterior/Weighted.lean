/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.PowerCutExterior.Identity
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Precomposition

/-!
# The signed cut of the inner reduced extension

The exterior unit projector is an actual base transfer. Precomposition
moves it across the cut, giving the reduced exterior case of Voevodsky's
Lemma 4.5.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme SmoothSite
open AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "G(" X ")" => product X T
local notation "F" => parameterProduct T

/-- Extend by the complement of the actual unit projector on the torus. -/
def torusReducedExtension {X Y : Cor k} (a : X ⟶ Y) : (F).obj X ⟶ (F).obj Y :=
  (F).map a ≫ (𝟙 _ - torusUnitProjector k Y)

/-- The reduced extension subtracts the actual target unit summand. -/
theorem torusReducedExtension_eq_sub {X Y : Cor k} (a : X ⟶ Y) :
    torusReducedExtension k a = (F).map a - (F).map a ≫ torusUnitProjector k Y := by
  unfold torusReducedExtension
  rw [Preadditive.comp_sub, Category.comp_id]

variable {X Y : SmoothSite (Spec (.of k))}

/-- Reducing the external factor subtracts precomposition by its original
unit projector. -/
theorem torusInnerReducedExtension_eq_sub (a : Cor.mk (G(X)) ⟶ Cor.mk (G(Y))) :
    torusInnerReducedExtension k a =
      torusInnerExtension k a -
        (F).map (torusUnitProjector k (Cor.mk X)) ≫ torusInnerExtension k a := by
  let X₀ := Cor.mk X
  let Y₀ := Cor.mk Y
  let a₀ : (F).obj X₀ ⟶ (F).obj Y₀ := a
  let f := (F).map a₀
  let s := torusDoubleSwap k X₀
  let t := torusDoubleSwap k Y₀
  let u₁ := torusUnitProjector k ((F).obj X₀)
  let u₂ := torusUnitProjector k ((F).obj Y₀)
  let u₀ := (F).map (torusUnitProjector k X₀)
  have h₁ : f ≫ u₂ = u₁ ≫ f := torusUnitProjector_naturality k a₀
  have h₂ : s ≫ u₁ = u₀ ≫ s := torusDoubleSwap_comp_outer k X₀
  have h : s ≫ f ≫ u₂ ≫ t = u₀ ≫ s ≫ f ≫ t := by
    calc
      _ = s ≫ (f ≫ u₂) ≫ t := congrArg (fun m => s ≫ m) (Category.assoc f u₂ t).symm
      _ = s ≫ (u₁ ≫ f) ≫ t := congrArg (fun m => s ≫ m ≫ t) h₁
      _ = (s ≫ u₁) ≫ f ≫ t := by simp only [Category.assoc]
      _ = (u₀ ≫ s) ≫ f ≫ t := congrArg (fun m => m ≫ f ≫ t) h₂
      _ = _ := Category.assoc u₀ s (f ≫ t)
  simp only [torusInnerReducedExtension, torusOuterReducedExtension, torusInnerExtension,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, Category.comp_id]
  change s ≫ f ≫ t - s ≫ f ≫ u₂ ≫ t = s ≫ f ≫ t - u₀ ≫ s ≫ f ≫ t
  exact congrArg (fun m => s ≫ f ≫ t - m) h

/-- At every sufficiently large exponent the native cut of the inner
reduced extension is the reduced exterior extension of the cut. -/
theorem exists_torusPowerCut_innerReducedExtension (a : Cor.mk (G(X)) ⟶ Cor.mk (G(Y))) :
    let b : Cor.mk (G(G(X))) ⟶ Cor.mk (G(G(Y))) :=
      torusInnerReducedExtension k (X := Cor.mk X) (Y := Cor.mk Y) a
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      a ∈ torusPowerCutDomain k X Y n ∧
      b ∈ torusPowerCutDomain k (G(X)) (G(Y)) n ∧
      ∀ (ha : a ∈ torusPowerCutDomain k X Y n)
        (hr : b ∈ torusPowerCutDomain k (G(X)) (G(Y)) n),
        torusPowerCut k (G(X)) (G(Y)) n ⟨b, hr⟩ =
          torusReducedExtension k (torusPowerCut k X Y n ⟨a, ha⟩) := by
  dsimp only
  obtain ⟨N₁, h₁⟩ := exists_torusPowerCut_innerExtension k (X := X) (Y := Y) a
  let b : Cor.mk (G(G(X))) ⟶ Cor.mk (G(G(Y))) :=
    torusInnerExtension k (X := Cor.mk X) (Y := Cor.mk Y) a
  let u := torusUnitProjector k (Cor.mk X)
  obtain ⟨N₂, h₂⟩ := exists_torusPowerCut_comp k
    (U := G(X)) (X := G(X)) (Y := G(Y)) u b
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨ha, hb, hcut⟩ := h₁ n ((le_max_left _ _).trans hn)
  obtain ⟨_, hc, hcomp⟩ := h₂ n ((le_max_right _ _).trans hn)
  let C := torusPowerCutDomain k (G(X)) (G(Y)) n
  let B : C := ⟨b, hb⟩
  let D : C := ⟨(F).map u ≫ b, hc⟩
  let br : Cor.mk (G(G(X))) ⟶ Cor.mk (G(G(Y))) :=
    torusInnerReducedExtension k (X := Cor.mk X) (Y := Cor.mk Y) a
  have hr : br ∈ C := by
    change torusInnerReducedExtension k (X := Cor.mk X) (Y := Cor.mk Y) a ∈ C
    rw [torusInnerReducedExtension_eq_sub k (X := X) (Y := Y) a]
    exact C.sub_mem hb hc
  refine ⟨ha, hr, fun ha' hr' => ?_⟩
  have hsub : (⟨br, hr'⟩ : C) = B - D :=
    Subtype.ext (torusInnerReducedExtension_eq_sub k (X := X) (Y := Y) a)
  rw [hsub, map_sub]
  change torusPowerCut k (G(X)) (G(Y)) n ⟨b, hb⟩ -
      torusPowerCut k (G(X)) (G(Y)) n ⟨(F).map u ≫ b, hc⟩ = _
  rw [hcomp hb hc, hcut ha' hb, ← torusUnitProjector_naturality]
  simp only [torusReducedExtension, Preadditive.comp_sub, Category.comp_id]

end AlgebraicGeometry.PresheafWithTransfers

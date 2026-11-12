/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.ReducedIdentity
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.AffineParameterSwap
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.InterchangeHomotopy
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.PowerCutExterior.Weighted

/-!
# Cutting the interchange homotopy

After moving the affine parameter out of the last torus position, a common
power cut can be taken on the chosen interchange and its prescribed
restrictions. The two endpoint cuts give the reduced extension of the cut
and the original signed correspondence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction
open AlgebraicGeometry.Cor

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => multiplicativeGroupObject Sₖ
local notation "F" => Cor.parameterProduct Gₘ
local notation "C" => Cor.parameterProduct (additiveGroupObject Sₖ)
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)
set_option quotPrecheck false in
local notation "σ(" X "," a ")" => γ (nativeAffineSection (.of k) (X).toSmoothSite a)
set_option quotPrecheck false in
local notation "D(" X "," Y "," n ")" =>
  torusPowerCutDomain k (X).toSmoothSite (Y).toSmoothSite n
set_option quotPrecheck false in
local notation "ρ(" X "," Y "," n ")" =>
  torusPowerCut k (X).toSmoothSite (Y).toSmoothSite n

/-- The cut of the actual interchange joins a reduced correspondence to the
reduced extension of its cut, relative to a finite family of zero restrictions. -/
theorem exists_torusPowerCut_relativeHomotopy {X Y : Cor k}
    (α : (F).obj X ⟶ (F).obj Y)
    (hα : (𝟙 _ - torusUnitProjector k X) ≫ α ≫ (𝟙 _ - torusUnitProjector k Y) = α)
    {ι : Type v} [Finite ι] (U : ι → Cor k)
    (f : ∀ i, (U i).toSmoothSite ⟶ X.toSmoothSite)
    (hf : ∀ i, (F).map (γ (f i)) ≫ α = 0)
    (hH : ∀ i, γ (affineLineCylinder.map (torusDoubleBaseMap k (f i))) ≫
      torusReducedExtensionsHomotopy k α = 0) :
    ∃ (w : X ⟶ Y) (K : (F).obj ((C).obj X) ⟶ (F).obj Y),
      (∀ i, γ (f i) ≫ w = 0) ∧
        (F).map (σ(X,0)) ≫ K = torusReducedExtension k w ∧
        (F).map (σ(X,1)) ≫ K = α ∧
        ∀ i, (F).map (γ (affineLineCylinder.map (f i))) ≫ K = 0 := by
  classical
  let H := torusReducedExtensionsHomotopy k α
  let A := (C).obj ((F).obj X)
  let B := (F).obj Y
  let a : (F).obj A ⟶ (F).obj B := torusAffineSwap k ((F).obj X) ≫ H
  let side (i : ι) : (C).obj ((F).obj (U i)) ⟶ A :=
    γ (affineLineCylinder.map (SmoothSite.productMap (f i) (𝟙 Gₘ)))
  let endpoint (v : Fin 2) : (F).obj X ⟶ A :=
    σ((F).obj X,if v = 0 then 0 else 1)
  obtain ⟨N, hN⟩ := exists_torusPowerCut_comp_family k
    (fun i => (U i).toSmoothSite) (fun _ => X.toSmoothSite) (fun _ => Y.toSmoothSite)
    (fun i => γ (f i)) (fun _ => α)
  obtain ⟨M, hM⟩ := exists_torusPowerCut_comp_family k
    (fun i => ((C).obj ((F).obj (U i))).toSmoothSite)
    (fun _ => A.toSmoothSite) (fun _ => B.toSmoothSite) side (fun _ => a)
  obtain ⟨L, hL⟩ := exists_torusPowerCut_comp_family k
    (fun _ : Fin 2 => ((F).obj X).toSmoothSite) (fun _ => A.toSmoothSite)
    (fun _ => B.toSmoothSite) endpoint (fun _ => a)
  obtain ⟨J, hJ⟩ := exists_torusPowerCut_innerReducedExtension k
    (X := X.toSmoothSite) (Y := Y.toSmoothSite) α
  let n := N + M + L + J + 1
  have hn : n ≠ 0 := by dsimp [n]; omega
  let hαN := hN n (by dsimp [n]; omega)
  let hside := hM n (by dsimp [n]; omega)
  let hend := hL n (by dsimp [n]; omega)
  obtain ⟨hαD, hinner, hcutInner⟩ := hJ n (by dsimp [n]; omega)
  let ha := (hend 0).1
  let w : X ⟶ Y := ρ(X,Y,n) ⟨α, hαD⟩
  let c : A ⟶ B := ρ(A,B,n) ⟨a, ha⟩
  let K : (F).obj ((C).obj X) ⟶ (F).obj Y := torusAffineSwap k X ≫ c
  have hw (i : ι) : γ (f i) ≫ w = 0 := by
    let a' : D(U i,Y,n) := ⟨(F).map (γ (f i)) ≫ α, (hαN i).2.1⟩
    have e : a' = 0 := Subtype.ext (hf i)
    exact ((hαN i).2.2 hαD (hαN i).2.1).symm.trans
      ((congrArg (ρ(U i,Y,n)) e).trans (map_zero _))
  have hsc (i : ι) : side i ≫ c = 0 := by
    have hz : (F).map (side i) ≫ a = 0 := by
      let v : ((F).obj (U i)).toSmoothSite ⟶ ((F).obj X).toSmoothSite :=
        SmoothSite.productMap (f i) (𝟙 Gₘ)
      let b : (C).obj ((F).obj ((F).obj (U i))) ⟶ (C).obj ((F).obj ((F).obj X)) :=
        γ (affineLineCylinder.map (torusDoubleBaseMap k (f i)))
      have h : (F).map (side i) ≫ torusAffineSwap k ((F).obj X) =
          torusAffineSwap k ((F).obj (U i)) ≫ b :=
        torusAffineSwap_graph_naturality k v
      calc
        _ = ((F).map (side i) ≫ torusAffineSwap k ((F).obj X)) ≫ H :=
          (Category.assoc _ _ _).symm
        _ = (torusAffineSwap k ((F).obj (U i)) ≫ b) ≫ H := congrArg (· ≫ H) h
        _ = torusAffineSwap k ((F).obj (U i)) ≫ (b ≫ H) := Category.assoc _ _ _
        _ = 0 := (congrArg (torusAffineSwap k ((F).obj (U i)) ≫ ·) (hH i)).trans
          comp_zero
    let U' := (C).obj ((F).obj (U i))
    let a' : D(U',B,n) := ⟨(F).map (side i) ≫ a, (hside i).2.1⟩
    have e : a' = 0 := Subtype.ext hz
    exact ((hside i).2.2 ha (hside i).2.1).symm.trans
      ((congrArg (ρ(U',B,n)) e).trans (map_zero _))
  have hendpoint₀ : endpoint 0 = σ((F).obj X,0) :=
    congrArg (fun t : k => σ((F).obj X,t)) (ite_eq_left (show (0 : Fin 2) = 0 from rfl))
  have hendpoint₁ : endpoint 1 = σ((F).obj X,1) :=
    congrArg (fun t : k => σ((F).obj X,t)) (ite_eq_right (show (1 : Fin 2) ≠ 0 from by decide))
  have hswap (t : k) :
      (F).map (σ((F).obj X,t)) ≫ a = σ((F).obj ((F).obj X),t) ≫ H :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ H) (torusAffineSwap_section k ((F).obj X) t))
  have hends := torusReducedExtensionsHomotopy_endpoints k α hα
  have ha₀ : (F).map (endpoint 0) ≫ a = torusInnerReducedExtension k α :=
    (congrArg (fun β => (F).map β ≫ a) hendpoint₀).trans ((hswap 0).trans hends.1)
  have ha₁ : (F).map (endpoint 1) ≫ a = torusOuterReducedExtension k α :=
    (congrArg (fun β => (F).map β ≫ a) hendpoint₁).trans ((hswap 1).trans hends.2)
  have hc₀ : endpoint 0 ≫ c = torusReducedExtension k w := by
    have e : (⟨(F).map (endpoint 0) ≫ a, (hend 0).2.1⟩ : D((F).obj X,B,n)) =
        ⟨torusInnerReducedExtension k α, hinner⟩ := Subtype.ext ha₀
    exact ((hend 0).2.2 ha (hend 0).2.1).symm.trans
      ((congrArg (ρ((F).obj X,B,n)) e).trans (hcutInner hαD hinner))
  have hc₁ : endpoint 1 ≫ c = α := by
    have hvalue : (F).map (endpoint 1) ≫ a =
        (F).map α - (F).map α ≫ torusUnitProjector k B := by
      rw [ha₁, torusOuterReducedExtension, Preadditive.comp_sub, Category.comp_id]
    have hred : (F).map α - (F).map α ≫ torusUnitProjector k B ∈ D((F).obj X,B,n) :=
      hvalue ▸ (hend 1).2.1
    have e : (⟨(F).map (endpoint 1) ≫ a, (hend 1).2.1⟩ : D((F).obj X,B,n)) =
        ⟨(F).map α - (F).map α ≫ torusUnitProjector k B, hred⟩ := Subtype.ext hvalue
    have hcut := torusPowerCut_reducedExterior k ((F).obj X).toSmoothSite B.toSmoothSite n hn α hred
    exact ((hend 1).2.2 ha (hend 1).2.1).symm.trans
      ((congrArg (ρ((F).obj X,B,n)) e).trans hcut)
  have hK (t : k) : (F).map (σ(X,t)) ≫ K = σ((F).obj X,t) ≫ c :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) (torusAffineSwap_section k X t))
  refine ⟨w, K, hw, ?_, ?_, ?_⟩
  · exact (hK 0).trans ((congrArg (· ≫ c) hendpoint₀.symm).trans hc₀)
  · exact (hK 1).trans ((congrArg (· ≫ c) hendpoint₁.symm).trans hc₁)
  · intro i
    have h : (F).map (γ (affineLineCylinder.map (f i))) ≫ torusAffineSwap k X =
        torusAffineSwap k (U i) ≫ side i := torusAffineSwap_graph_naturality k (f i)
    calc
      _ = ((F).map (γ (affineLineCylinder.map (f i))) ≫ torusAffineSwap k X) ≫ c :=
        (Category.assoc _ _ _).symm
      _ = (torusAffineSwap k (U i) ≫ side i) ≫ c := congrArg (· ≫ c) h
      _ = torusAffineSwap k (U i) ≫ (side i ≫ c) := Category.assoc _ _ _
      _ = 0 := (congrArg (torusAffineSwap k (U i) ≫ ·) (hsc i)).trans comp_zero

end AlgebraicGeometry.PresheafWithTransfers

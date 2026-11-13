/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Precomposition
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.ReducedIdentity
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Evaluated
public import Colib.AlgebraicTopology.DoldKan.NormalizedRepresentatives

/-!
# Reflecting normalized boundaries by the signed power cut

Choose a common exponent on a bounding simplex and its finitely many faces.
The cut of the original bounding simplex then has the required zeroth face
and vanishes on every positive face.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme AlgebraicTopology.NormalizedMooreComplex

variable (k : Type u) [Field k] (Y : Cor k)

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "F" => Cor.parameterProduct Gₘ
local notation "P" => Functor.obj (representableLarge k) Y
local notation "T" => torusCancellationTarget k Y
set_option quotPrecheck false in
local notation "S(" X "," P₀ ")" => (Cor.simplexProductCosimplicial X).op ⋙ (P₀).obj
set_option quotPrecheck false in
local notation "D(" X "," m ")" => Cor.torusPowerCutDomain k (X).toSmoothSite Y.toSmoothSite m
set_option quotPrecheck false in
local notation "ρ(" X "," m ")" => Cor.torusPowerCut k (X).toSmoothSite Y.toSmoothSite m
set_option quotPrecheck false in
local notation "E(" w ")" => (F).map w - (F).map w ≫ torusUnitProjector k Y

/-- The original Suslin comparison reflects normalized boundaries using
eventual compatibility of the power cut and its reduced exterior identity. -/
theorem torusCancellationMap_reflects_normalizedBoundary
    (X : Cor k) (n : ℕ) (x : sections P (Cor.simplexProduct X n))
    (hx : IsBoundary (S(X,T)) n
      ((torusCancellationMap k Y).hom.app (op (Cor.simplexProduct X n)) x)) :
    IsBoundary (S(X,P)) n x := by
  classical
  obtain ⟨b, hb, hb₀⟩ := hx
  let U := Cor.simplexProduct X n
  let V := Cor.simplexProduct X (n + 1)
  let δ (i : Fin (n + 2)) : U ⟶ V := (Cor.simplexProductCosimplicial X).δ i
  let L := torusCancellationLift k Y
  let a : (F).obj V ⟶ (F).obj Y := (L.hom.app (op V) b).down
  let w : U ⟶ Y := (show ULift.{u + 1} (U ⟶ Y) from x).down
  have hw : (ULift.up w : sections P U) = x := by
    exact ULift.up_down x
  have hface (i : Fin (n + 2)) :
      (F).map (δ i) ≫ a = (L.hom.app (op U) (transfer T (δ i) b)).down :=
    (torusCancellationLift_transfer_apply k Y (δ i) b).symm
  obtain ⟨N, hN⟩ := Cor.exists_torusPowerCut_comp_family k
    (fun _ : Fin (n + 2) => U.toSmoothSite) (fun _ => V.toSmoothSite) (fun _ => Y.toSmoothSite)
    δ (fun _ => a)
  let m := max 1 N
  have hm₀ : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  let h := hN m (le_max_right _ _)
  let hc (i : Fin (n + 2)) := (h i).2.1
  let c := ρ(V,m) ⟨a, (h 0).1⟩
  have hcut' (i : Fin (n + 2)) :
      ρ(U,m) ⟨(F).map (δ i) ≫ a, hc i⟩ = δ i ≫ c := (h i).2.2 (h 0).1 (hc i)
  have hz (i : Fin (n + 1)) : δ i.succ ≫ c = 0 := by
    have hi : transfer T (δ i.succ) b = 0 := hb i
    have hi' : (F).map (δ i.succ) ≫ a = 0 := by
      rw [hface i.succ, hi, map_zero]
      rfl
    have e : (⟨(F).map (δ i.succ) ≫ a, hc i.succ⟩ : D(U,m)) = 0 :=
      Subtype.ext hi'
    simpa only [e, map_zero] using (hcut' i.succ).symm
  have hf₀ : (F).map (δ 0) ≫ a = E(w) := by
    rw [hface 0]
    change transfer T (δ 0) b = (torusCancellationMap k Y).hom.app (op U) x at hb₀
    rw [hb₀, ← hw, torusCancellationLift_map_app_apply]
  have hred : E(w) ∈ D(U,m) := hf₀ ▸ hc 0
  have e : (⟨(F).map (δ 0) ≫ a, hc 0⟩ : D(U,m)) = ⟨E(w), hred⟩ := Subtype.ext hf₀
  have h₀ : δ 0 ≫ c = w := by
    rw [← hcut' 0, e]
    exact Cor.torusPowerCut_reducedExterior k U.toSmoothSite Y.toSmoothSite m hm₀ w hred
  refine ⟨ULift.up c, ?_, ?_⟩
  · intro i
    change transfer P (δ i.succ) (ULift.up c) = 0
    rw [representableLarge_transfer_apply, hz i]
    rfl
  · change transfer P (δ 0) (ULift.up c) = x
    rw [representableLarge_transfer_apply, h₀]
    exact hw

end AlgebraicGeometry.PresheafWithTransfers

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Evaluated
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.InterchangeCut
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.RelativeInterchange
public import Colib.AlgebraicGeometry.Simplex.RelativeAffineLine

/-!
# Surjectivity of the reduced torus comparison on normalized homology

Apply the relative interchange to the signed representative of a cycle.
The cut gives a source cycle, and its affine-line homotopy gives a normalized
boundary for the difference from the original target cycle.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction
open AlgebraicTopology.NormalizedMooreComplex
open scoped Simplicial

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "A₁" => additiveGroupObject Sₖ
local notation "F" => Cor.parameterProduct (multiplicativeGroupObject Sₖ)
local notation "C" => Cor.parameterProduct A₁
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)
set_option quotPrecheck false in
local notation "S(" P₁ "," X ")" => (Cor.simplexProductCosimplicial X).op ⋙ (P₁).obj
set_option quotPrecheck false in
local notation "σ(" X "," a ")" => γ (nativeAffineSection (.of k) (X).toSmoothSite a)

private def faceIndex (n : ℕ) : Type :=
  match n with
  | .zero => Fin 0
  | .succ m => Fin (m + 2)

private theorem finite_faceIndex (n : ℕ) : Finite (faceIndex n) := by
  cases n with
  | zero => exact inferInstanceAs (Finite (Fin 0))
  | succ n => exact inferInstanceAs (Finite (Fin (n + 2)))

private def coface (X : Cor k) (n : ℕ) (i : faceIndex n) :
    (Cor.simplexProduct X (n - 1)).toSmoothSite ⟶ (Cor.simplexProduct X n).toSmoothSite := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    exact SmoothSite.productMap (𝟙 X.toSmoothSite) ((AlgebraicSimplex.cosimplicialSmoothSite k).δ i)

/-- Every normalized target cycle is the image of a normalized source
cycle modulo a normalized boundary. -/
theorem torusCancellationMap_surjective_mod_normalizedBoundaries (Y X : Cor k) (n : ℕ)
    (y : sections (torusCancellationTarget k Y) (Cor.simplexProduct X n))
    (hy : IsCycle (S(torusCancellationTarget k Y,X)) n y) :
    ∃ x : sections ((representableLarge k).obj Y) (Cor.simplexProduct X n),
      IsCycle (S((representableLarge k).obj Y,X)) n x ∧
        IsBoundary (S(torusCancellationTarget k Y,X)) n
          (y - (torusCancellationMap k Y).hom.app (op (Cor.simplexProduct X n)) x) := by
  classical
  let V := Cor.simplexProduct X n
  let T := torusCancellationTarget k Y
  let P := (representableLarge k).obj Y
  let L := torusCancellationLift k Y
  let Q := torusCancellationProjection k Y
  let a : (F).obj V ⟶ (F).obj Y := (L.hom.app (op V) y).down
  have ha : L.hom.app (op V) y = ULift.up a := (ULift.up_down _).symm
  have hred : (𝟙 _ - torusUnitProjector k V) ≫ a ≫ (𝟙 _ - torusUnitProjector k Y) = a :=
    ((exists_torusCancellationLift_app_eq_iff k Y V a).1 ⟨y, ha⟩).symm
  let : Finite (faceIndex n) := finite_faceIndex n
  let f := coface k X n
  have hface (i : faceIndex n) : (F).map (γ (f i)) ≫ a = 0 := by
    have hz : transfer T (γ (f i)) y = 0 := by
      cases n with
      | zero => exact Fin.elim0 i
      | succ n => exact hy i
    have h := torusCancellationLift_transfer_apply k Y (γ (f i)) y
    rw [hz, map_zero] at h
    exact h.symm
  have hH (i : faceIndex n) :
      γ (affineLineCylinder.map (torusDoubleBaseMap k (f i))) ≫
        torusReducedExtensionsHomotopy k a = 0 := by
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      exact torusReducedExtensionsHomotopy_simplex_face_eq_zero k X.toSmoothSite i a (hface i)
  obtain ⟨w, K, hw, hK₀, hK₁, hKface⟩ :=
    exists_torusPowerCut_relativeHomotopy k a hred
      (fun _ : faceIndex n => Cor.simplexProduct X (n - 1)) f hface hH
  let project (W : Cor k) (b : (F).obj W ⟶ (F).obj Y) : sections T W :=
    Q.hom.app (op W) (ULift.up b)
  have hProject {W W' : Cor k} (β : W' ⟶ W) (b : (F).obj W ⟶ (F).obj Y) :
      transfer T β (project W b) = project W' ((F).map β ≫ b) :=
    torusCancellationProjection_transfer_apply k Y β b
  let z := project ((C).obj V) K
  have hz₀ : transfer T (σ(V,0)) z =
      (torusCancellationMap k Y).hom.app (op V) (ULift.up w) := by
    have hcut : (F).map (σ(V,0)) ≫ K = (F).map w - (F).map w ≫ torusUnitProjector k Y :=
      hK₀.trans (torusReducedExtension_eq_sub k w)
    let y₀ := (torusCancellationMap k Y).hom.app (op V) (ULift.up w)
    have hl : L.hom.app (op V) y₀ =
        ULift.up ((F).map w - (F).map w ≫ torusUnitProjector k Y) :=
      torusCancellationLift_map_app_apply k Y V w
    exact (hProject (σ(V,0)) K).trans ((congrArg (project V) hcut).trans
      ((congrArg (fun b : ULift.{u + 1} ((F).obj V ⟶ (F).obj Y) => Q.hom.app (op V) b)
        hl.symm).trans (torusCancellationLift_projection_app_apply k Y V y₀)))
  have hz₁ : transfer T (σ(V,1)) z = y := by
    exact (hProject (σ(V,1)) K).trans ((congrArg (project V) hK₁).trans
      ((congrArg (fun b : ULift.{u + 1} ((F).obj V ⟶ (F).obj Y) => Q.hom.app (op V) b)
        ha.symm).trans (torusCancellationLift_projection_app_apply k Y V y)))
  let T₀ := (toPresheaf k).obj T
  let T₁ := (AlgebraicSimplex.parameterReindex k A₁).obj T₀
  have hz : IsCycle ((AlgebraicSimplex.simplicialPresheaf k T₁).flip.obj
      (op X.toSmoothSite)) n z := by
    cases n with
    | zero => trivial
    | succ n =>
      intro i
      let j : faceIndex (n + 1) := i
      let β := γ (affineLineCylinder.map (f j))
      change transfer T β z = 0
      exact (hProject β K).trans
        ((congrArg (project _) (hKface j)).trans (map_zero _))
  have h :=
    AlgebraicSimplex.nativeAffineSection_sub_isNormalizedBoundary k T₀ X.toSmoothSite n z hz
  change IsBoundary (S(T,X)) n (transfer T (σ(V,1)) z - transfer T (σ(V,0)) z) at h
  rw [hz₁, hz₀] at h
  refine ⟨ULift.up w, ?_, h⟩
  cases n with
  | zero => trivial
  | succ n =>
    intro i
    change transfer P (γ (f i)) (ULift.up w) = 0
    exact (representableLarge_transfer_apply k (γ (f i)) w).trans
      (congrArg ULift.up (hw i))

end AlgebraicGeometry.PresheafWithTransfers

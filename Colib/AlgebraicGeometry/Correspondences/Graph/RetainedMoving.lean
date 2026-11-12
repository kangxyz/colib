/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.MovingEndpoints
public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedPencilDifference

/-!
# Moving endpoints from whole ideal supports

The actual retained family and its constant pole give the signed
ideal-support endpoints on the native cylinder.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/Moving/OneSided/MovingEndpoints.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `bfd9ea719794339333d60ddda5dbae58d5cf623c`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k] {S X Y : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t] (q : X ⟶ S) (r : Y ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  [IsSeparated r] [SmoothOfRelativeDimension 1 r]
  (f : X ⟶ Y) (hf : f ≫ r = q)
  (L T : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property T]

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)
local notation "C" => pullback q r
local notation "G" => relativeGraphIdeal q r f hf

variable (a₀ a₁ : Γ(L, ⊤)) (b : Γ(T, ⊤))

local notation "A₀" => zeroScheme C L a₀
local notation "A₁" => zeroScheme C L a₁
local notation "B" => zeroScheme C T b

set_option maxHeartbeats 800000 in
-- The endpoint comparisons check the raw support spans on the constructed smooth sites.
/-- Finite-flat pencil sections supported in the original good open at one
give the two literal moving endpoints on the native cylinder. -/
theorem hasMovingEndpoints_of_retainedPencil
    (witnesses : RetainedPencilWitnesses (k := k) t q r L T a₀ a₁ b)
    {V : SmoothSite (Spec (.of k))} (j : V ⟶ W) [IsOpenImmersion j.left]
    (hb : IsEffectiveCartierDivisor B)
    (hprod : A₀ = G * B)
    (haV : Set.range ((A₁).subschemeι ≫ pullback.snd q r) ⊆ Set.range j.left)
    (hbV : Set.range ((B).subschemeι ≫ pullback.snd q r) ⊆ Set.range j.left) :
    HasMovingEndpoints (k := k)
      (SmoothSite.homMk (X := U) (Y := W) f
        ((Category.assoc f r t).symm.trans (congrArg (fun g => g ≫ t) hf))) j := by
  let α := retainedPencilDifferenceFromWitnesses (k := k) t q r L T a₀ a₁ b witnesses
  let h₀ := nativeRetainedZero_finite_flat (k := k) t q r L a₀ a₁
    (_hFamilyFin := witnesses.familyFinite) (_hFamilyFlat := witnesses.familyFlat)
  let h₁ := nativeRetainedOne_finite_flat (k := k) t q r L a₀ a₁
    (_hFamilyFin := witnesses.familyFinite) (_hFamilyFlat := witnesses.familyFlat)
  let := h₀.1
  let := h₀.2
  let := h₁.1
  let := h₁.2
  let poleIdeal : (pullback q r).IdealSheafData := B
  let : IsFinite (poleIdeal.subschemeι ≫ pullback.fst q r) := witnesses.poleFinite
  let : Flat (poleIdeal.subschemeι ≫ pullback.fst q r) := witnesses.poleFlat
  let zeroSpan := retainedZeroSpan (k := k) t q r L a₀ h₀.1 h₀.2
  let oneSpan := retainedZeroSpan (k := k) t q r L a₁ h₁.1 h₁.2
  let poleSpan := retainedZeroSpan (k := k) t q r T b witnesses.poleFinite witnesses.poleFlat
  have hA₀ : zeroSpan = retainedIdealSpan (k := k) t q r A₀ := rfl
  have hA₁ : oneSpan = retainedIdealSpan (k := k) t q r A₁ := rfl
  have hB : poleSpan = retainedIdealSpan (k := k) t q r poleIdeal := rfl
  have hZero : (graphFunctor k).map (nativeAffineSection (.of k) U 0) ≫ α =
      zeroSpan - poleSpan :=
    (retainedPencilDifferenceFromWitnesses_zero (k := k) t q r L T a₀ a₁ b witnesses).eq
  have hOne : (graphFunctor k).map (nativeAffineSection (.of k) U 1) ≫ α =
      oneSpan - poleSpan :=
    (retainedPencilDifferenceFromWitnesses_one (k := k) t q r L T a₀ a₁ b witnesses).eq
  exact hasMovingEndpoints_of_retainedIdealSpans (k := k) t q r f hf A₀ A₁ poleIdeal
    j hb hprod haV hbV α
    (hZero.trans (congrArg₂ (· - ·) hA₀ hB))
    (hOne.trans (congrArg₂ (· - ·) hA₁ hB))

end AlgebraicGeometry.Cor

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitUnitSecondNative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitSquare
public import Colib.KTheory.Waldhausen.Iterated.ScalarRectangleLiftOps

/-! The original split-unit routes, their exact rotation, and the whole genuine native unit square.
Adapted from `OriginalUnitSquareSimplex.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Convexity Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem relative_hcomp_apply {E F : LoopPrespectrum.{u}} {a b c : E ⟶ F}
    {H H' : Homotopy a b} {K K' : Homotopy b c}
    (J : H.RelHomotopy H') (L : K.RelHomotopy K')
    (n : ℕ) (r t : unitInterval) (x : E.space n) :
    (J.hcomp L).level n (r, (t, x)) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        J.level n (r, (⟨2 * t,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x))
      else L.level n (r, (⟨2 * t - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, x)) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

private theorem hcomp_evaluate {A B : Type*} [TopologicalSpace A] {a b c : A}
    {p p' : Path a b} {q q' : Path b c} (J : p.Homotopy p') (K : q.Homotopy q')
    (v : A → B) (F G : unitInterval → unitInterval → B)
    (hJ : ∀ r t, v (J (r, t)) = F r t) (hK : ∀ r t, v (K (r, t)) = G r t)
    (r t : unitInterval) :
    v ((J.hcomp K) (r, t)) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        F r ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      else G r ⟨2 * t - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := by
  rw [Path.Homotopy.hcomp_apply]
  split
  · exact hJ _ _
  · exact hK _ _

private theorem right_route_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    (boundedAboveFlatPerfectNormalizedRightUnitRouteComparison f).level n (r, (t, x)) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        (boundedAboveFlatPerfectNormalizedCompTrackComparison (𝟙 X) f).level n
          (r, (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x))
      else (Homotopy.RelHomotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap f)
        (boundedAboveFlatPerfectNormalizedIdTrackComparison X)).level n
          (r, (⟨2 * t - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, x)) :=
  relative_hcomp_apply
    ((boundedAboveFlatPerfectNormalizedCompTrackComparison (𝟙 X) f).cast
      (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Category.id_comp f)) rfl)
    ((Homotopy.RelHomotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap f)
      (boundedAboveFlatPerfectNormalizedIdTrackComparison X)).cast rfl (Category.comp_id _)) n r t x

private theorem right_route_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n
      ((rightFirstParameter.hcomp rightSecondParameter) (r, t), x) =
      (boundedAboveFlatPerfectNormalizedRightUnitRouteComparison f).level n (r, (t, x)) := by
  refine Eq.trans ?_ (right_route_value f n r t x).symm
  exact hcomp_evaluate rightFirstParameter rightSecondParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ (boundedAboveFlatPerfectNormalizedCompTrackComparison (𝟙 X) f).level n (r, (t, x)))
    (fun r t ↦ (Homotopy.RelHomotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap f)
      (boundedAboveFlatPerfectNormalizedIdTrackComparison X)).level n (r, (t, x)))
    (fun r t ↦ rightFirst_native f n r t x) (fun r t ↦ rightSecond_native f n r t x) r t

private theorem left_route_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    (boundedAboveFlatPerfectNormalizedLeftUnitRouteComparison f).level n (r, (t, x)) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        (boundedAboveFlatPerfectNormalizedCompTrackComparison f (𝟙 Y)).level n
          (r, (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x))
      else ((boundedAboveFlatPerfectNormalizedIdTrackComparison Y).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap f)).level n
          (r, (⟨2 * t - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩, x)) :=
  relative_hcomp_apply
    ((boundedAboveFlatPerfectNormalizedCompTrackComparison f (𝟙 Y)).cast
      (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Category.comp_id f)) rfl)
    (((boundedAboveFlatPerfectNormalizedIdTrackComparison Y).postcomp
      (boundedAboveFlatPerfectPullbackPrespectrumMap f)).cast rfl (Category.id_comp _)) n r t x

private theorem left_route_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n
      ((leftFirstParameter.hcomp leftSecondParameter) (r, t), x) =
      (boundedAboveFlatPerfectNormalizedLeftUnitRouteComparison f).level n (r, (t, x)) := by
  refine Eq.trans ?_ (left_route_value f n r t x).symm
  exact hcomp_evaluate leftFirstParameter leftSecondParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ (boundedAboveFlatPerfectNormalizedCompTrackComparison f (𝟙 Y)).level n (r, (t, x)))
    (fun r t ↦ ((boundedAboveFlatPerfectNormalizedIdTrackComparison Y).postcomp
      (boundedAboveFlatPerfectPullbackPrespectrumMap f)).level n (r, (t, x)))
    (fun r t ↦ leftFirst_native f n r t x) (fun r t ↦ leftSecond_native f n r t x) r t

/-- The scalar unit-route comparison evaluates to the entire original comparison. -/
theorem routes_native : HomotopyLift (simplex f) routesParameter
    (boundedAboveFlatPerfectOriginalUnitRoutesComparison f) :=
  HomotopyLift.trans (simplex f) (HomotopyLift.symm (simplex f) (right_route_native f))
    (HomotopyLift.trans (simplex f) (normalized_native f) (left_route_native f))

private theorem squareBoundary_apply {E F : LoopPrespectrum.{u}}
    {f₀ g₀ f₁ g₁ f₀' g₀' f₁' g₁' : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}
    (S : H₀.Square H₁ L M)
    (H₀' : Homotopy f₀' g₀') (H₁' : Homotopy f₁' g₁')
    (L' : Homotopy f₀' f₁') (M' : Homotopy g₀' g₁')
    (h₀ : ∀ n, H₀'.level n = H₀.level n) (h₁ : ∀ n, H₁'.level n = H₁.level n)
    (hL : ∀ n, L'.level n = L.level n) (hM : ∀ n, M'.level n = M.level n)
    (n : ℕ) (r t : unitInterval) (x : E.space n) :
    (S.ofBoundaryLevels H₀' H₁' L' M' h₀ h₁ hL hM).level n (r, (t, x)) =
      S.level n (r, (t, x)) := rfl

private theorem target_evaluate {A B : Type*} [TopologicalSpace A] {a b : A}
    {p q : Path a b} (J : p.Homotopy q) (v : A → B)
    (F : unitInterval → unitInterval → B)
    (hJ : ∀ r t, v (J (r, t)) = F r t) (t : unitInterval) :
    v (q t) = F 1 t :=
  (congrArg v (J.apply_one t)).symm.trans (hJ 1 t)

private theorem right_composition_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightCompositionPath t, x) =
      (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (𝟙 X) f).level n (t, x) := by
  exact (target_evaluate rightFirstParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ (boundedAboveFlatPerfectNormalizedCompTrackComparison (𝟙 X) f).level n (r, (t, x)))
    (fun r t ↦ rightFirst_native f n r t x) t).trans
      (((boundedAboveFlatPerfectNormalizedCompTrackComparison (𝟙 X) f).level n).apply_one (t, x))

private theorem left_composition_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftCompositionPath t, x) =
      (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f (𝟙 Y)).level n (t, x) := by
  exact (target_evaluate leftFirstParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ (boundedAboveFlatPerfectNormalizedCompTrackComparison f (𝟙 Y)).level n (r, (t, x)))
    (fun r t ↦ leftFirst_native f n r t x) t).trans
      (((boundedAboveFlatPerfectNormalizedCompTrackComparison f (𝟙 Y)).level n).apply_one (t, x))

private theorem right_unit_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightUnitPath t, x) =
      (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap f)
        (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X)).level n (t, x) := by
  exact (target_evaluate rightSecondParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ (Homotopy.RelHomotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap f)
        (boundedAboveFlatPerfectNormalizedIdTrackComparison X)).level n (r, (t, x)))
    (fun r t ↦ rightSecond_native f n r t x) t).trans
      (((Homotopy.RelHomotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap f)
        (boundedAboveFlatPerfectNormalizedIdTrackComparison X)).level n).apply_one (t, x))

private theorem left_unit_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftUnitPath t, x) =
      ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy Y).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap f)).level n (t, x) := by
  exact (target_evaluate leftSecondParameter
    (fun z ↦ prespectrumSimplexFamily (simplex f) n (z, x))
    (fun r t ↦ ((boundedAboveFlatPerfectNormalizedIdTrackComparison Y).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap f)).level n (r, (t, x)))
    (fun r t ↦ leftSecond_native f n r t x) t).trans
      ((((boundedAboveFlatPerfectNormalizedIdTrackComparison Y).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap f)).level n).apply_one (t, x))

private theorem rotation_native : HomotopyLift (simplex f) (Path.Homotopy.rotate routesParameter)
    (Homotopy.RelHomotopy.rotate (boundedAboveFlatPerfectOriginalUnitRoutesComparison f)) :=
  HomotopyLift.rectangleRotate (simplex f) (right_composition_native f) (right_unit_native f)
    (left_composition_native f) (left_unit_native f) (routes_native f)

private theorem contraction_native :
  let L := (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap f)
    (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X)).cast rfl (Category.comp_id _)
  let M := ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy Y).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap f)).cast rfl (Category.id_comp _)
  HomotopyLift (simplex f)
    ((Path.Homotopy.transRefl rightUnitPath).symm.hcomp
      (Path.Homotopy.refl leftUnitPath.symm))
    ((Homotopy.RelHomotopy.transRefl L).symm.hcomp (Homotopy.RelHomotopy.refl M.symm)) :=
  HomotopyLift.hcomp (simplex f)
    (HomotopyLift.symm (simplex f) (RectanglePathLift.transRefl (simplex f) (right_unit_native f)))
    (PathLift.refl (simplex f) (PathLift.symm (simplex f) (left_unit_native f)))

/-- Every value of the original geometric unit square lies in this actual common simplex. -/
theorem square_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (squareParameter (r, t), x) =
      (boundedAboveFlatPerfectPullbackPrespectrumUnitSquare f).level n (r, (t, x)) := by
  unfold boundedAboveFlatPerfectPullbackPrespectrumUnitSquare
  dsimp only
  rw [squareBoundary_apply]
  exact HomotopyLift.toSquare (simplex f)
    (HomotopyLift.trans (simplex f) (rotation_native f) (contraction_native f)) n r t x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex

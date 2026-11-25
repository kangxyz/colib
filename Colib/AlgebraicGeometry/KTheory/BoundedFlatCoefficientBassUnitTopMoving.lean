/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitTopNative
public import Colib.KTheory.Waldhausen.Iterated.SimplexLiftSquareOperations

/-! The original three-piece moving square of the raw Bass identity top.
Adapted from Quillen `CoefficientPolynomialSpanUnitTop.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The two dyadic cuts and the
reversed negative clock are unchanged. The target contraction is separate. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTop

local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
local notation "unitRotatedParam" => BoundedFlatPerfectOriginalUnitSquareSimplex.rotatedParameter

local notation "bassProjParameter" => BoundedFlatCoefficientBassProjectionPath.parameter

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

private theorem map_projection {d : ℕ} (α : ⦋4⦌ ⟶ ⦋d⦌) (t : unitInterval) :
    embed α (bassProjParameter t) =
      ((binaryPath (α.toOrderHom 0) (α.toOrderHom 1) (α.toOrderHom 2)).symm.trans
        (binaryPath (α.toOrderHom 0) (α.toOrderHom 3) (α.toOrderHom 4))) t :=
  map_trans_values _ _ _ _ _ (fun t ↦ map_binaryPath α 0 1 2 (unitInterval.symm t))
    (map_binaryPath α 0 3 4) t

/-- Reindex the actual unit square and retain its four literal scalar path boundaries. -/
def unitFaceSquare {d : ℕ} (α : ⦋7⦌ ⟶ ⦋d⦌) :
    ParameterSquare
      ((binaryPath (α.toOrderHom 0) (α.toOrderHom 1) (α.toOrderHom 2)).symm.trans
        (binaryPath (α.toOrderHom 0) (α.toOrderHom 4) (α.toOrderHom 5)))
      (Path.refl (StdSimplex.single (α.toOrderHom 7)))
      (binaryPath (α.toOrderHom 2) (α.toOrderHom 3) (α.toOrderHom 7))
      (binaryPath (α.toOrderHom 5) (α.toOrderHom 6) (α.toOrderHom 7)) :=
  ParameterSquare.ofBoundaryPaths
    ((ParameterSquare.ofBoundary unitRotatedParam).reindex α) _ _ _ _
      (fun t ↦ (map_trans_values _ _ _ _ _
        (fun t ↦ map_binaryPath α 0 1 2 (unitInterval.symm t))
        (map_binaryPath α 0 4 5) t).symm)
      (fun _ ↦ (StdSimplex.map_single _ _).symm)
      (fun t ↦ (map_binaryPath α 2 3 7 t).symm)
      (fun t ↦ (map_binaryPath α 5 6 7 t).symm)

/-- The original unit square on the ordered plus face. -/
abbrev plusSquare := unitFaceSquare plusFace
/-- The original unit square on the minus face with both paths reversed. -/
abbrev minusSquare := (unitFaceSquare minusFace).reversePaths

/-- The lower row word of the original middle grid in the merged simplex. -/
def middleStart : Path (StdSimplex.single 12 : StdSimplex ℝ (Fin 25))
    (StdSimplex.single 14) := (binaryPath 10 11 12).symm.trans (binaryPath 10 13 14)
/-- The upper row word of the original middle grid in the merged simplex. -/
def middleEnd : Path (StdSimplex.single 22 : StdSimplex ℝ (Fin 25))
    (StdSimplex.single 24) := (binaryPath 20 21 22).symm.trans (binaryPath 20 23 24)

/-- The whole product square, with its two scalar row paths and two exact common-node columns. -/
def middleSquare : ParameterSquare middleStart middleEnd
    (binaryPath 12 17 22) (binaryPath 14 19 24) where
  parameter := middleParameter.{u}
  at_zero t := by
    change StdSimplex.map middleFace.toOrderHom
      (SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 0,
        bassProjParameter t)) = _
    rw [Path.source, SimplexGrid.parameter_row, ← StdSimplex.map_comp]
    exact map_projection (SimplexGrid.rowFace 2 4 0 ≫ middleFace) t
  at_one t := by
    change StdSimplex.map middleFace.toOrderHom
      (SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 1,
        bassProjParameter t)) = _
    rw [Path.target, SimplexGrid.parameter_row, ← StdSimplex.map_comp]
    exact map_projection (SimplexGrid.rowFace 2 4 2 ≫ middleFace) t
  left r := by
    change StdSimplex.map middleFace.toOrderHom
      (SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 r,
        bassProjParameter 0)) = _
    rw [Path.source, SimplexGrid.parameter_column, ← StdSimplex.map_comp]
    exact map_binaryPath (SimplexGrid.columnFace 2 4 2 ≫ middleFace) 0 1 2 r
  right r := by
    change StdSimplex.map middleFace.toOrderHom
      (SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 r,
        bassProjParameter 1)) = _
    rw [Path.target, SimplexGrid.parameter_column, ← StdSimplex.map_comp]
    exact map_binaryPath (SimplexGrid.columnFace 2 4 4 ≫ middleFace) 0 1 2 r

/-- These are entire scalar join equalities, proved before any native-family evaluation. -/
theorem plus_middle_join (r : unitInterval) :
    plusSquare.parameter (r, 1) = middleSquare.{u}.parameter (r, 0) :=
  (plusSquare.right r).trans (middleSquare.left r).symm

theorem middle_minus_join (r : unitInterval) :
    middleSquare.{u}.parameter (r, 1) = minusSquare.parameter (r, 0) :=
  (middleSquare.right r).trans (minusSquare.left r).symm

/-- The original positive, moving-middle and reversed negative pieces keep their association. -/
def movingSquare := plusSquare.pastePaths (middleSquare.{u}.pastePaths minusSquare)

/-- The prespectrum map induced by the coefficient polynomial projection. -/
abbrev polynomialMap := K (polynomialProjection P a)
/-- The original coefficient Bass-square comparison map. -/
abbrev comparisonMap := boundedAboveFlatCoefficientBassSquareComparison P a

/-- The unchanged native moving square, before its identity-cylinder contractions. -/
def movingNative := HomotopyPushout.identicalLegMovingSquare
  (polynomialMap P a) (polynomialMap P a)
  (boundedAboveFlatCoefficientPolynomialSquareHomotopy P (𝟙 a))
  (coneSquareIdentityTrack (polynomialMap P a))
  (boundedAboveFlatCoefficientIdentityHomotopy P a)
  (boundedAboveFlatCoefficientPolynomialIdentityHomotopy P a)
  (boundedAboveFlatCoefficientPolynomialIdentitySquare P a)

private theorem native_paste_value {E F : LoopPrespectrum.{u}}
    {f₀ g₀ h₀ f₁ g₁ h₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {K₀ : Homotopy g₀ h₀} {K₁ : Homotopy g₁ h₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} {N : Homotopy h₀ h₁}
    (J : H₀.Square H₁ L M) (J' : K₀.Square K₁ M N)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.pastePaths J').level n (r, (s, x)) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        J.level n (r, (⟨2 * s,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x))
      else J'.level n (r, (⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

private theorem mapped_paste_evaluate {d : ℕ} {U : Type*}
    {a₀ b₀ c₀ a₁ b₁ c₁ : StdSimplex ℝ (Fin (d + 1))}
    {p₀ : Path a₀ b₀} {p₁ : Path a₁ b₁} {q₀ : Path b₀ c₀} {q₁ : Path b₁ c₁}
    {l : Path a₀ a₁} {m : Path b₀ b₁} {j : Path c₀ c₁}
    {E F : LoopPrespectrum.{u}} {f₀ g₀ h₀ f₁ g₁ h₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {K₀ : Homotopy g₀ h₀} {K₁ : Homotopy g₁ h₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} {N : Homotopy h₀ h₁}
    (Q : ParameterSquare p₀ p₁ l m) (R : ParameterSquare q₀ q₁ m j)
    (J : H₀.Square H₁ L M) (J' : K₀.Square K₁ M N) (n : ℕ) (x : E.space n)
    (e : StdSimplex ℝ (Fin (d + 1)) → U) (v : F.space n → U)
    (hQ : ∀ r s, e (Q.parameter (r, s)) = v (J.level n (r, (s, x))))
    (hR : ∀ r s, e (R.parameter (r, s)) = v (J'.level n (r, (s, x))))
    (r s : unitInterval) :
    e ((Q.pastePaths R).parameter (r, s)) = v ((J.pastePaths J').level n (r, (s, x))) := by
  rw [ParameterSquare.pastePaths_apply, native_paste_value]
  split
  · exact hQ _ _
  · exact hR _ _

/-- All three pieces paste to the actual native moving square, before the original postmap. -/
theorem moving_native : SquareLift (simplex P a) movingSquare.{u}
    ((movingNative P a).postcompose (comparisonMap P a)) := by
  intro n r s x
  change prespectrumSimplexFamily (simplex P a) n (movingSquare.parameter (r, s), x) =
    (comparisonMap P a).map n ((movingNative P a).level n (r, (s, x)))
  unfold movingSquare movingNative HomotopyPushout.identicalLegMovingSquare
  refine mapped_paste_evaluate _ _ _ _ n x
    (fun z ↦ prespectrumSimplexFamily (simplex P a) n (z, x))
    ((comparisonMap P a).map n) ?_ ?_ r s
  · intro r s
    exact plus_native P a n r s x
  · intro r s
    refine mapped_paste_evaluate _ _ _ _ n x
      (fun z ↦ prespectrumSimplexFamily (simplex P a) n (z, x))
      ((comparisonMap P a).map n) ?_ ?_ r s
    · intro r s
      exact middle_native P a n r s x
    · intro r s
      exact minus_native P a n r (unitInterval.symm s) x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTop

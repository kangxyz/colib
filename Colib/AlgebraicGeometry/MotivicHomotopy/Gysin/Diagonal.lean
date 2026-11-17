/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.DiagonalGeometry
public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.ClosedImmersion
import Colib.Util.References
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # The Gysin triangle of the diagonal -/

@[expose] public noncomputable section

open AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Pretriangulated
open SmoothSite

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

/-- The canonical additive sheafification on the Nisnevich correspondence site. -/
local instance diagonalGysinCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- The canonical additive sheafification on the smooth Nisnevich site. -/
local instance diagonalGysinSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

attribute [local instance] gysinAbelian

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))
local notation "M" => effectiveSmoothMotive k
local notation "L" => effectiveLefschetzTwistFunctor k

set_option Elab.async false in
set_option maxHeartbeats 600000 in
-- Identify the iterate at the literal smooth motive of the centre.
/-- The Lefschetz power for the diagonal codimension is the power for the dimension. -/
theorem diagonalLefschetzPower_eq (X : Sm) (d : ℕ) :
    (Stabilization.iterate L (d + d - d)).obj ((M).obj X) =
      (Stabilization.iterate L d).obj ((M).obj X) :=
  congrArg (fun n => (Stabilization.iterate L n).obj ((M).obj X)) (Nat.add_sub_cancel_left d d)

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
-- Use the original diagonal and its specified dimension.
/-- The diagonal Gysin map with codimension equal to the pure dimension of the scheme. -/
@[colib_tag "COL-1240"]
def effectiveDiagonalGysin (X : Sm) {d : ℕ} (h : RelativeDimension X.hom d) :
    (M).obj (product X X) ⟶ (Stabilization.iterate L d).obj ((M).obj X) :=
  effectiveGysin k (productDiagonal X) (relativeDimension_smoothSquare X h) h ≫
    eqToHom (diagonalLefschetzPower_eq k X d)

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
-- Transport the original diagonal triangle along the exponent equality.
/-- The Gysin triangle of the diagonal with its codimension normalized to the dimension. -/
@[colib_tag "COL-1240"]
def effectiveDiagonalGysinTriangle (X : Sm) {d : ℕ} (h : RelativeDimension X.hom d) :
    Triangle (EffectiveMotivesMinus k) :=
  (effectiveGysinTriangle k (productDiagonal X) (relativeDimension_smoothSquare X h) h).ofIso₃
    (eqToIso (diagonalLefschetzPower_eq k X d))

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
-- Apply the closed immersion result to the original diagonal.
/-- The diagonal Gysin triangle uses the original open complement and boundary. -/
@[colib_tag "COL-1240",
  colib_ref "Voevodsky2000TriangulatedMotives" "Proposition 3.5.4" "specialization"
    "The Gysin triangle of the diagonal of a pure-dimensional smooth scheme"]
theorem effectiveDiagonalGysinTriangle_distinguished (X : Sm) {d : ℕ}
    (h : RelativeDimension X.hom d) :
    effectiveDiagonalGysinTriangle k X h ∈ distTriang (EffectiveMotivesMinus k) := by
  let T := effectiveGysinTriangle k (productDiagonal X) (relativeDimension_smoothSquare X h) h
  exact T.ofIso₃_distinguished (eqToIso (diagonalLefschetzPower_eq k X d))
    (effectiveGysinTriangle_distinguished k (productDiagonal X)
      (relativeDimension_smoothSquare X h) h)

end AlgebraicGeometry.MotivicHomotopy

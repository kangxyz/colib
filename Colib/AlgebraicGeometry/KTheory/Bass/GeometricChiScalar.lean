/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.DoubleLaurentInclusion
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeInvolution

/-! # The whole geometric comparison and original double-cone permutation -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
universe u w
namespace KTheory.Bass.GeometricChiPermutation
open GeometricConeInterchange

open GeometricSquareInterchange SquareConeStrength
open PushoutStrength PushoutCofiberSquare

/-- The original outer target inclusion viewed as a natural map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiScalar.lean:28"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
def targetMap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :=
  coneInclusion (comparison (geometricSquare F))

/-- The original upper cone cell at its unchanged height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiScalar.lean:32"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
def upperMap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (r : unitInterval) :=
  left (geometricSquare F).left.hom (geometricSquare F).hom.left ≫
    diagramHomotopyAt (coneNull (comparison (geometricSquare F)))
      (coneNull_naturality (comparison (geometricSquare F))) r

/-- The original lower cone cell at its unchanged height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiScalar.lean:38"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
def lowerMap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (r : unitInterval) :=
  right (geometricSquare F).left.hom (geometricSquare F).hom.left ≫
    diagramHomotopyAt (coneNull (comparison (geometricSquare F)))
      (coneNull_naturality (comparison (geometricSquare F))) r

/-- The original overlap cell retaining both independent interval coordinates. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiScalar.lean:44"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
def overlapMap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (r s : unitInterval) :=
  diagramHomotopyAt (glue (geometricSquare F).left.hom (geometricSquare F).hom.left)
    (glue_naturality (geometricSquare F).left.hom (geometricSquare F).hom.left) s ≫
    diagramHomotopyAt (coneNull (comparison (geometricSquare F)))
      (coneNull_naturality (comparison (geometricSquare F))) r

/-- The whole original target cell is the permutation after evaluation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiScalar.lean:51"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
theorem target_scalar (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (z : ((coneFunctor.obj F).obj (laurent.op.obj X)).space n) :
    ((coneFunctor.map (targetMap F)).app X).map n
      (((GeometricConeInterchange.eta
        (laurentProjection (.of (ULift.{u} ℤ))) F).hom.app X).map n z) =
      (permutation F X).hom.map n
        (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n z) := by
  induction z using Cell.inductionOn (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n
  · rw [permutation_target_target]
    rfl
  · rw [permutation_target_upper]
    rfl
  · rw [permutation_target_lower]
    rfl
  · rename_i r s y
    rw [permutation_target_overlap]
    change Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s
      (Cell.target (F.mapArrow.mapArrow.obj (square X)) n ((F.map (𝟙 _)).map n y)) = _
    rw [F.map_id]
    rfl

/-- The whole original upper cell is the permutation after evaluation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiScalar.lean:73"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
theorem upper_scalar (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r : unitInterval) (z : ((coneFunctor.obj F).obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.map (upperMap F r)).app X).map n (((GeometricConeInterchange.eta
        (polynomialProjection (.of (ULift.{u} ℤ))) F).hom.app X).map n z) =
      (permutation F X).hom.map n
        (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r z) := by
  induction z using Cell.inductionOn (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
  · rw [permutation_upper_target]
    rfl
  · rw [permutation_upper_upper]
    rfl
  · rw [permutation_upper_lower]
    rfl
  · rename_i t v y
    rw [permutation_upper_overlap]
    change Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t v
      (Cell.upper (F.mapArrow.mapArrow.obj (square X)) n r ((F.map (𝟙 _)).map n y)) = _
    rw [F.map_id]
    rfl

/-- The whole original lower cell is the permutation after evaluation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiScalar.lean:94"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
theorem lower_scalar (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r : unitInterval) (z : ((coneFunctor.obj F).obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.map (lowerMap F r)).app X).map n (((GeometricConeInterchange.eta
        (polynomialProjection (.of (ULift.{u} ℤ))) F).hom.app X).map n z) =
      (permutation F X).hom.map n
        (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r z) := by
  induction z using Cell.inductionOn (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
  · rw [permutation_lower_target]
    rfl
  · rw [permutation_lower_upper]
    rfl
  · rw [permutation_lower_lower]
    rfl
  · rename_i t v y
    rw [permutation_lower_overlap]
    change Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t v
      (Cell.lower (F.mapArrow.mapArrow.obj (square X)) n r ((F.map (𝟙 _)).map n y)) = _
    rw [F.map_id]
    rfl

/-- The whole original overlap cell is the permutation after evaluation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiScalar.lean:115"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
theorem overlap_scalar (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r s : unitInterval) (z : ((coneFunctor.obj F).obj (X)).space n) :
    ((coneFunctor.map (overlapMap F r s)).app X).map n z =
      (permutation F X).hom.map n
        (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s z) := by
  induction z using Cell.inductionOn (F.mapArrow.mapArrow.obj (square (X))) n
  · rw [permutation_overlap_target]
    rfl
  · rw [permutation_overlap_upper]
    rfl
  · rw [permutation_overlap_lower]
    rfl
  · rw [permutation_overlap_overlap]
    rfl

end KTheory.Bass.GeometricChiPermutation

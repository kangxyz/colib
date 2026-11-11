/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeTarget
public import Colib.Topology.Prespectrum.StrictDoubleSquareConeCells

/-!
# Sixteen original cells of the geometric double-cone permutation

Every cell keeps its original parameters. The two complete parameter blocks
are exchanged and the coefficient point is transported by the actual opposite
swap with its factors in the specified order. The empty factor is handled by
the literal original identity. These are formulas for the constructed map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.GeometricConeInterchange
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)

/-- The actual target/target cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:34"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_target_target (n : ℕ)
    (x : (F.obj (laurent.op.obj (laurent.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (x))) =
      Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n ((F.map (baseProductSwapMap
        (laurentProjection (.of (ULift.{u} ℤ))) (laurentProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) := rfl

/-- The actual target/upper cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:45"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_target_upper (n : ℕ) (t : unitInterval)
    (x : (F.obj (polynomial.op.obj (laurent.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.upper
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (x))) =
      Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n ((F.map (baseProductSwapMap
        (polynomialProjection (.of (ULift.{u} ℤ))) (laurentProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) := rfl

/-- The actual target/lower cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:56"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_target_lower (n : ℕ) (t : unitInterval)
    (x : (F.obj (polynomial.op.obj (laurent.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.lower
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (x))) =
      Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n ((F.map (baseProductSwapMap
        (polynomialProjection (.of (ULift.{u} ℤ))) (laurentProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) := rfl

/-- The actual target/overlap cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:67"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_target_overlap (n : ℕ) (t v : unitInterval)
    (x : (F.obj (laurent.op.obj X)).space n) :
    (permutation F X).hom.map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (x))) =
      Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t v (Cell.target
        (F.mapArrow.mapArrow.obj (square X)) n (x)) := rfl

/-- The actual upper/target cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:76"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_upper_target (n : ℕ) (r : unitInterval)
    (x : (F.obj (laurent.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (x))) =
      Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.upper
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n r ((F.map (baseProductSwapMap
        (laurentProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) := rfl

/-- The actual upper/upper cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:87"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_upper_upper (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) =
      Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r ((F.map (baseProductSwapMap
        (polynomialProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) := rfl

/-- The actual upper/lower cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:98"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_upper_lower (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) =
      Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r ((F.map (baseProductSwapMap
        (polynomialProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) := rfl

/-- The actual upper/overlap cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:109"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_upper_overlap (n : ℕ) (r t v : unitInterval)
    (x : (F.obj (polynomial.op.obj X)).space n) :
    (permutation F X).hom.map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (x))) =
      Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t v (Cell.upper
        (F.mapArrow.mapArrow.obj (square X)) n r (x)) := rfl

/-- The actual lower/target cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:118"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_lower_target (n : ℕ) (r : unitInterval)
    (x : (F.obj (laurent.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (x))) =
      Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.lower
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n r ((F.map (baseProductSwapMap
        (laurentProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) := rfl

/-- The actual lower/upper cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:129"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_lower_upper (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) =
      Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r ((F.map (baseProductSwapMap
        (polynomialProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) := rfl

/-- The actual lower/lower cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:140"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_lower_lower (n : ℕ) (r t : unitInterval)
    (x : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    (permutation F X).hom.map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) =
      Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r ((F.map (baseProductSwapMap
        (polynomialProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ)))
        X.unop).op).map n x)) := rfl

/-- The actual lower/overlap cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:151"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_lower_overlap (n : ℕ) (r t v : unitInterval)
    (x : (F.obj (polynomial.op.obj X)).space n) :
    (permutation F X).hom.map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (x))) =
      Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t v (Cell.lower
        (F.mapArrow.mapArrow.obj (square X)) n r (x)) := rfl

/-- The actual overlap/target cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:160"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_overlap_target (n : ℕ) (r s : unitInterval)
    (x : (F.obj (laurent.op.obj X)).space n) :
    (permutation F X).hom.map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.target
        (F.mapArrow.mapArrow.obj (square X)) n (x))) =
      Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n r s (x)) := by
  change Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n r s ((F.map (𝟙 _)).map n x)) = _
  rw [F.map_id]
  rfl

/-- The actual overlap/upper cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:173"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_overlap_upper (n : ℕ) (r s t : unitInterval)
    (x : (F.obj (polynomial.op.obj X)).space n) :
    (permutation F X).hom.map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.upper
        (F.mapArrow.mapArrow.obj (square X)) n t (x))) =
      Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r s (x)) := by
  change Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r s ((F.map (𝟙 _)).map n x))
        = _
  rw [F.map_id]
  rfl

/-- The actual overlap/lower cell retains its specified swap and both complete parameter blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:187"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_overlap_lower (n : ℕ) (r s t : unitInterval)
    (x : (F.obj (polynomial.op.obj X)).space n) :
    (permutation F X).hom.map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.lower
        (F.mapArrow.mapArrow.obj (square X)) n t (x))) =
      Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r s (x)) := by
  change Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r s ((F.map (𝟙 _)).map n x))
        = _
  rw [F.map_id]
  rfl

/-- The actual overlap/overlap cell retains its specified swap and both complete parameter
        blocks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeCells.lean:202"
  "adaptation" "Original sixteen geometric cells with literal swaps and all parameters."]
theorem permutation_overlap_overlap (n : ℕ) (r s t v : unitInterval)
    (x : (F.obj X).space n) :
    (permutation F X).hom.map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n t v (x))) =
      Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n t v (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n r s (x)) := rfl

end KTheory.Bass.GeometricConeInterchange

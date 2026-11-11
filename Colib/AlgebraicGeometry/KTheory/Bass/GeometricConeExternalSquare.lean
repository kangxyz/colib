/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeExternalCells

/-!
# External-index compatibility of the actual geometric double-cone permutation

The original inverse two-factor move satisfies the actual inverse braid square.
All sixteen original quotient cells preserve both complete interval blocks.
The seven empty-factor cases use their original identity maps explicitly.
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

/-- The inverse external move retains the literal opposite internal-swap direction. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:31"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem externalInverse_swap_op {S T U : Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (r : U ⟶ (Spec (.of (ULift.{u} ℤ))))
    (X : Scheme.{u}) :
    ((baseProductFunctor r).map (baseProductSwapMap p q X)).op ≫
        (externalInverse p q r X).op =
      (externalInverse q p r X).op ≫
        (baseProductSwapMap p q ((baseProductFunctor r).obj X)).op := by
  rw [externalInverse_op, externalInverse_op]
  apply (cancel_mono (baseProductMoveExternal p q r X).op).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← baseProductMoveExternal_swap_op]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- The actual coefficient functor preserves the inverse geometric square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:45"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem externalInverse_map_swap {S T U : Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (r : U ⟶ (Spec (.of (ULift.{u} ℤ))))
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}) :
    F.map ((baseProductFunctor r).map (baseProductSwapMap p q X)).op ≫
        F.map (externalInverse p q r X).op =
      F.map (externalInverse q p r X).op ≫
        F.map (baseProductSwapMap p q ((baseProductFunctor r).obj X)).op := by
  rw [← F.map_comp, ← F.map_comp, externalInverse_swap_op]

variable {U : Scheme.{u}} (q : U ⟶ (Spec (.of (ULift.{u} ℤ))))
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)

/-- External-index compatibility on the complete original target/target cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:58"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_target_target (n : ℕ)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj (laurent.op.obj X)))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n (Cell.target (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (laurent.op.obj X))) n (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n (Cell.target (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n (Cell.target (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (laurent.op.obj X))) n (x)))) = (permutation F ((baseProductFunctor q).op.obj
        X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n (Cell.target (((baseProductFunctor q).op
        ⋙ F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (x))))
  rw [permutation_target_target, externalTransport_target_target, externalTransport_target_target,
    permutation_target_target]
  exact congrArg (fun z => Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n (Cell.target (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj ((baseProductFunctor q).op.obj X)))) n (z)))
    (congrArg (fun k => k.map n x) (externalInverse_map_swap (laurentProjection (.of (ULift.{u}
        ℤ))) (laurentProjection (.of (ULift.{u} ℤ))) q F X.unop))

/-- External-index compatibility on the complete original target/upper cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:86"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_target_upper (n : ℕ) (t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (laurent.op.obj X)))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n (Cell.upper (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (laurent.op.obj X))) n t (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n (Cell.upper (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n (Cell.upper (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (laurent.op.obj X))) n t (x)))) = (permutation F ((baseProductFunctor q).op.obj
        X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n (Cell.upper (((baseProductFunctor q).op
        ⋙ F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (x))))
  rw [permutation_target_upper, externalTransport_upper_target, externalTransport_target_upper,
    permutation_target_upper]
  exact congrArg (fun z => Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n t (Cell.target (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n (z)))
    (congrArg (fun k => k.map n x) (externalInverse_map_swap (polynomialProjection (.of
        (ULift.{u} ℤ))) (laurentProjection (.of (ULift.{u} ℤ))) q F X.unop))

/-- External-index compatibility on the complete original target/lower cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:114"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_target_lower (n : ℕ) (t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (laurent.op.obj X)))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n (Cell.lower (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (laurent.op.obj X))) n t (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n (Cell.lower (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n (Cell.lower (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (laurent.op.obj X))) n t (x)))) = (permutation F ((baseProductFunctor q).op.obj
        X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n (Cell.lower (((baseProductFunctor q).op
        ⋙ F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (x))))
  rw [permutation_target_lower, externalTransport_lower_target, externalTransport_target_lower,
    permutation_target_lower]
  exact congrArg (fun z => Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n t (Cell.target (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n (z)))
    (congrArg (fun k => k.map n x) (externalInverse_map_swap (polynomialProjection (.of
        (ULift.{u} ℤ))) (laurentProjection (.of (ULift.{u} ℤ))) q F X.unop))

/-- External-index compatibility on the complete original target/overlap cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:142"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_target_overlap (n : ℕ) (t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj X))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n (Cell.overlap (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (laurent.op.obj X))) n t v (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n (Cell.overlap (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.target ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n (Cell.overlap (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (laurent.op.obj X))) n t v (x)))) = (permutation F ((baseProductFunctor
        q).op.obj X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.target ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n (Cell.overlap (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (x))))
  rw [permutation_target_overlap, externalTransport_overlap_target,
        externalTransport_target_overlap,
    permutation_target_overlap]

/-- External-index compatibility on the complete original upper/target cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:166"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_upper_target (n : ℕ) (r : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj (polynomial.op.obj X)))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r (Cell.target (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (polynomial.op.obj X))) n (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r (Cell.target (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square
        X)) n r (Cell.target (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n (x)))) = (permutation F ((baseProductFunctor q).op.obj
        X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.target (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (x))))
  rw [permutation_upper_target, externalTransport_target_upper, externalTransport_upper_target,
    permutation_upper_target]
  exact congrArg (fun z => Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n (Cell.upper (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj ((baseProductFunctor q).op.obj X)))) n r (z)))
    (congrArg (fun k => k.map n x) (externalInverse_map_swap (laurentProjection (.of (ULift.{u}
        ℤ))) (polynomialProjection (.of (ULift.{u} ℤ))) q F X.unop))

/-- External-index compatibility on the complete original upper/upper cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:194"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_upper_upper (n : ℕ) (r t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (polynomial.op.obj X)))).space
        n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r (Cell.upper (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (polynomial.op.obj X))) n t (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square
        X)) n r (Cell.upper (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)))) = (permutation F ((baseProductFunctor q).op.obj
        X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))))
  rw [permutation_upper_upper, externalTransport_upper_upper, externalTransport_upper_upper,
    permutation_upper_upper]
  exact congrArg (fun z => Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n t (Cell.upper (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n r (z)))
    (congrArg (fun k => k.map n x) (externalInverse_map_swap (polynomialProjection (.of
        (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ))) q F X.unop))

/-- External-index compatibility on the complete original upper/lower cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:223"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_upper_lower (n : ℕ) (r t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (polynomial.op.obj X)))).space
        n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r (Cell.lower (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (polynomial.op.obj X))) n t (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square
        X)) n r (Cell.lower (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)))) = (permutation F ((baseProductFunctor q).op.obj
        X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))))
  rw [permutation_upper_lower, externalTransport_lower_upper, externalTransport_upper_lower,
    permutation_upper_lower]
  exact congrArg (fun z => Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n t (Cell.upper (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n r (z)))
    (congrArg (fun k => k.map n x) (externalInverse_map_swap (polynomialProjection (.of
        (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ))) q F X.unop))

/-- External-index compatibility on the complete original upper/overlap cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:252"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_upper_overlap (n : ℕ) (r t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj X))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r (Cell.overlap (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (polynomial.op.obj X))) n t v (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.upper ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square
        X)) n r (Cell.overlap (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t v (x)))) = (permutation F ((baseProductFunctor q).op.obj
        X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.upper ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (x))))
  rw [permutation_upper_overlap, externalTransport_overlap_upper, externalTransport_upper_overlap,
    permutation_upper_overlap]

/-- External-index compatibility on the complete original lower/target cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:275"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_lower_target (n : ℕ) (r : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj (polynomial.op.obj X)))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r (Cell.target (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (polynomial.op.obj X))) n (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r (Cell.target (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square
        X)) n r (Cell.target (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n (x)))) = (permutation F ((baseProductFunctor q).op.obj
        X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.target (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (x))))
  rw [permutation_lower_target, externalTransport_target_lower, externalTransport_lower_target,
    permutation_lower_target]
  exact congrArg (fun z => Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n (Cell.lower (F.mapArrow.mapArrow.obj (square
        (laurent.op.obj ((baseProductFunctor q).op.obj X)))) n r (z)))
    (congrArg (fun k => k.map n x) (externalInverse_map_swap (laurentProjection (.of (ULift.{u}
        ℤ))) (polynomialProjection (.of (ULift.{u} ℤ))) q F X.unop))

/-- External-index compatibility on the complete original lower/upper cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:303"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_lower_upper (n : ℕ) (r t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (polynomial.op.obj X)))).space
        n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r (Cell.upper (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (polynomial.op.obj X))) n t (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square
        X)) n r (Cell.upper (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)))) = (permutation F ((baseProductFunctor q).op.obj
        X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.upper (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))))
  rw [permutation_lower_upper, externalTransport_upper_lower, externalTransport_lower_upper,
    permutation_lower_upper]
  exact congrArg (fun z => Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n t (Cell.lower (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n r (z)))
    (congrArg (fun k => k.map n x) (externalInverse_map_swap (polynomialProjection (.of
        (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ))) q F X.unop))

/-- External-index compatibility on the complete original lower/lower cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:332"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_lower_lower (n : ℕ) (r t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj (polynomial.op.obj X)))).space
        n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r (Cell.lower (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (polynomial.op.obj X))) n t (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square
        X)) n r (Cell.lower (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t (x)))) = (permutation F ((baseProductFunctor q).op.obj
        X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.lower (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (x))))
  rw [permutation_lower_lower, externalTransport_lower_lower, externalTransport_lower_lower,
    permutation_lower_lower]
  exact congrArg (fun z => Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square
        ((baseProductFunctor q).op.obj X))) n t (Cell.lower (F.mapArrow.mapArrow.obj (square
        (polynomial.op.obj ((baseProductFunctor q).op.obj X)))) n r (z)))
    (congrArg (fun k => k.map n x) (externalInverse_map_swap (polynomialProjection (.of
        (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ))) q F X.unop))

/-- External-index compatibility on the complete original lower/overlap cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:361"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_lower_overlap (n : ℕ) (r t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj X))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r (Cell.overlap (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square (polynomial.op.obj X))) n t v (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.lower ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square
        X)) n r (Cell.overlap (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square
        (polynomial.op.obj X))) n t v (x)))) = (permutation F ((baseProductFunctor q).op.obj
        X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.lower ((coneFunctor.obj ((baseProductFunctor
        q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap (((baseProductFunctor
        q).op ⋙ F).mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (x))))
  rw [permutation_lower_overlap, externalTransport_overlap_lower, externalTransport_lower_overlap,
    permutation_lower_overlap]

/-- External-index compatibility on the complete original overlap/target cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:384"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_overlap_target (n : ℕ) (r s : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (laurent.op.obj X))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.target (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square X)) n (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.target (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square X)) n (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.target (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square X)) n (x)))) = (permutation F ((baseProductFunctor q).op.obj X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.overlap ((coneFunctor.obj
        ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.target
        (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square X)) n (x))))
  rw [permutation_overlap_target, externalTransport_target_overlap,
        externalTransport_overlap_target,
    permutation_overlap_target]

/-- External-index compatibility on the complete original overlap/upper cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:407"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_overlap_upper (n : ℕ) (r s t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj X))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.upper (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square X)) n t (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.upper (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square X)) n t (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.upper (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square X)) n t (x)))) = (permutation F ((baseProductFunctor q).op.obj X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.overlap ((coneFunctor.obj
        ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.upper
        (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square X)) n t (x))))
  rw [permutation_overlap_upper, externalTransport_upper_overlap, externalTransport_overlap_upper,
    permutation_overlap_upper]

/-- External-index compatibility on the complete original overlap/lower cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:429"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_overlap_lower (n : ℕ) (r s t : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj (polynomial.op.obj X))).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.lower (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square X)) n t (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.lower (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square X)) n t (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.lower (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square X)) n t (x)))) = (permutation F ((baseProductFunctor q).op.obj X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.overlap ((coneFunctor.obj
        ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.lower
        (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square X)) n t (x))))
  rw [permutation_overlap_lower, externalTransport_lower_overlap, externalTransport_overlap_lower,
    permutation_overlap_lower]

/-- External-index compatibility on the complete original overlap/overlap cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:451"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_overlap_overlap (n : ℕ) (r s t v : unitInterval)
    (x : (F.obj ((baseProductFunctor q).op.obj X)).space n) :
    ((permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X).map n
        (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.overlap (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square X)) n t v (x))) =
      ((externalTransport q F).app X ≫ (permutation F ((baseProductFunctor q).op.obj
        X)).hom).map n (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙
        F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap (((baseProductFunctor q).op ⋙
        F).mapArrow.mapArrow.obj (square X)) n t v (x))) := by
  change ((externalTransport q F).app X).map n ((permutation ((baseProductFunctor q).op ⋙ F)
        X).hom.map n
    (Cell.overlap ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.overlap (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
        (square X)) n t v (x)))) = (permutation F ((baseProductFunctor q).op.obj X)).hom.map n
      (((externalTransport q F).app X).map n (Cell.overlap ((coneFunctor.obj
        ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap
        (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj (square X)) n t v (x))))
  rw [permutation_overlap_overlap, externalTransport_overlap_overlap,
        externalTransport_overlap_overlap,
    permutation_overlap_overlap]

/-- The entire original double quotient commutes with the actual inverse external transport. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:474"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_square :
    (permutation ((baseProductFunctor q).op ⋙ F) X).hom ≫ (externalTransport q F).app X =
      (externalTransport q F).app X ≫
        (permutation F ((baseProductFunctor q).op.obj X)).hom := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  refine Cell.inductionOn
    ((coneFunctor.obj ((baseProductFunctor q).op ⋙ F)).mapArrow.mapArrow.obj (square X))
    n x ?_ ?_ ?_ ?_
  · intro y
    refine Cell.inductionOn (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
      (square (laurent.op.obj X))) n y ?_ ?_ ?_ ?_
    · intro z
      exact permutation_external_target_target q F X n z
    · intro t z
      exact permutation_external_target_upper q F X n t z
    · intro t z
      exact permutation_external_target_lower q F X n t z
    · intro t v z
      exact permutation_external_target_overlap q F X n t v z
  · intro r y
    refine Cell.inductionOn (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
      (square (polynomial.op.obj X))) n y ?_ ?_ ?_ ?_
    · intro z
      exact permutation_external_upper_target q F X n r z
    · intro t z
      exact permutation_external_upper_upper q F X n r t z
    · intro t z
      exact permutation_external_upper_lower q F X n r t z
    · intro t v z
      exact permutation_external_upper_overlap q F X n r t v z
  · intro r y
    refine Cell.inductionOn (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
      (square (polynomial.op.obj X))) n y ?_ ?_ ?_ ?_
    · intro z
      exact permutation_external_lower_target q F X n r z
    · intro t z
      exact permutation_external_lower_upper q F X n r t z
    · intro t z
      exact permutation_external_lower_lower q F X n r t z
    · intro t v z
      exact permutation_external_lower_overlap q F X n r t v z
  · intro r s y
    refine Cell.inductionOn (((baseProductFunctor q).op ⋙ F).mapArrow.mapArrow.obj
      (square X)) n y ?_ ?_ ?_ ?_
    · intro z
      exact permutation_external_overlap_target q F X n r s z
    · intro t z
      exact permutation_external_overlap_upper q F X n r s t z
    · intro t z
      exact permutation_external_overlap_lower q F X n r s t z
    · intro t v z
      exact permutation_external_overlap_overlap q F X n r s t v z

/-- The actual inverse external-index transformation commutes with the natural permutation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalSquare.lean:531"
  "adaptation" "Original inverse braid square on all sixteen whole quotient cells."]
theorem permutation_external_naturality :
    (permutationNatIso ((baseProductFunctor q).op ⋙ F)).hom ≫ externalTransport q F =
      externalTransport q F ≫
        Functor.whiskerLeft (baseProductFunctor q).op (permutationNatIso F).hom := by
  ext X : 2
  exact permutation_external_square q F X

end KTheory.Bass.GeometricConeInterchange

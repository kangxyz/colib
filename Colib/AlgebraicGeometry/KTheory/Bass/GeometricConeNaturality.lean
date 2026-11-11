/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeCells
public import Colib.Topology.Prespectrum.StrictSquareCellInduction

/-!
# Naturality of the original geometric two-cone permutation

Naturality is checked on all sixteen original quotient cells. It uses ordinary
naturality of the given spectrum transformation at the actual scheme swap, or
the actual base-product swap square for a scheme map. All original interval
parameters remain free.
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
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}


/-- Diagram naturality keeps the full original target/target cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:35"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_target_target (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (z : (F.obj (laurent.op.obj (laurent.op.obj X))).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (z))) := by
  change (permutation G X).hom.map n (Cell.target ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n (Cell.target (G.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n
        ((h.app (laurent.op.obj (laurent.op.obj X))).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.target (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n
        (z))))
  rw [permutation_target_target, permutation_target_target]
  exact congrArg (fun z => Cell.target ((coneFunctor.obj G).mapArrow.mapArrow.obj (square X)) n
        (Cell.target (G.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (z)))
    (congrArg (fun k => k.map n z)
      (h.naturality (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op).symm)

/-- Diagram naturality keeps the full original target/upper cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:58"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_target_upper (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (t : unitInterval)
    (z : (F.obj (polynomial.op.obj (laurent.op.obj X))).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.upper
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.upper
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (z))) := by
  change (permutation G X).hom.map n (Cell.target ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n (Cell.upper (G.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t
        ((h.app (polynomial.op.obj (laurent.op.obj X))).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.upper (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t
        (z))))
  rw [permutation_target_upper, permutation_target_upper]
  exact congrArg (fun z => Cell.upper ((coneFunctor.obj G).mapArrow.mapArrow.obj (square X)) n t
        (Cell.target (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (z)))
    (congrArg (fun k => k.map n z)
      (h.naturality (baseProductSwapMap (polynomialProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op).symm)

/-- Diagram naturality keeps the full original target/lower cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:81"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_target_lower (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (t : unitInterval)
    (z : (F.obj (polynomial.op.obj (laurent.op.obj X))).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.lower
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.lower
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (z))) := by
  change (permutation G X).hom.map n (Cell.target ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n (Cell.lower (G.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t
        ((h.app (polynomial.op.obj (laurent.op.obj X))).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.lower (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t
        (z))))
  rw [permutation_target_lower, permutation_target_lower]
  exact congrArg (fun z => Cell.lower ((coneFunctor.obj G).mapArrow.mapArrow.obj (square X)) n t
        (Cell.target (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (z)))
    (congrArg (fun k => k.map n z)
      (h.naturality (baseProductSwapMap (polynomialProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op).symm)

/-- Diagram naturality keeps the full original target/overlap cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:104"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_target_overlap (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (t v :
        unitInterval)
    (z : (F.obj (laurent.op.obj X)).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (z))) := by
  change (permutation G X).hom.map n (Cell.target ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n (Cell.overlap (G.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v
        ((h.app (laurent.op.obj X)).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.overlap (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v
        (z))))
  rw [permutation_target_overlap, permutation_target_overlap]
  all_goals rfl

/-- Diagram naturality keeps the full original upper/target cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:124"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_upper_target (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (z : (F.obj (laurent.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (z))) := by
  change (permutation G X).hom.map n (Cell.upper ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r (Cell.target (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        ((h.app (laurent.op.obj (polynomial.op.obj X))).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        (z))))
  rw [permutation_upper_target, permutation_upper_target]
  exact congrArg (fun z => Cell.target ((coneFunctor.obj G).mapArrow.mapArrow.obj (square X)) n
        (Cell.upper (G.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n r (z)))
    (congrArg (fun k => k.map n z)
      (h.naturality (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).symm)

/-- Diagram naturality keeps the full original upper/upper cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:147"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_upper_upper (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (z : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) := by
  change (permutation G X).hom.map n (Cell.upper ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r (Cell.upper (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        ((h.app (polynomial.op.obj (polynomial.op.obj X))).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        (z))))
  rw [permutation_upper_upper, permutation_upper_upper]
  exact congrArg (fun z => Cell.upper ((coneFunctor.obj G).mapArrow.mapArrow.obj (square X)) n t
        (Cell.upper (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r (z)))
    (congrArg (fun k => k.map n z)
      (h.naturality (baseProductSwapMap (polynomialProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).symm)

/-- Diagram naturality keeps the full original upper/lower cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:170"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_upper_lower (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (z : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) := by
  change (permutation G X).hom.map n (Cell.upper ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r (Cell.lower (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        ((h.app (polynomial.op.obj (polynomial.op.obj X))).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        (z))))
  rw [permutation_upper_lower, permutation_upper_lower]
  exact congrArg (fun z => Cell.lower ((coneFunctor.obj G).mapArrow.mapArrow.obj (square X)) n t
        (Cell.upper (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r (z)))
    (congrArg (fun k => k.map n z)
      (h.naturality (baseProductSwapMap (polynomialProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).symm)

/-- Diagram naturality keeps the full original upper/overlap cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:193"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_upper_overlap (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t v :
        unitInterval)
    (z : (F.obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (z))) := by
  change (permutation G X).hom.map n (Cell.upper ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r (Cell.overlap (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        t v ((h.app (polynomial.op.obj X)).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        t v (z))))
  rw [permutation_upper_overlap, permutation_upper_overlap]
  all_goals rfl

/-- Diagram naturality keeps the full original lower/target cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:213"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_lower_target (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (z : (F.obj (laurent.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (z))) := by
  change (permutation G X).hom.map n (Cell.lower ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r (Cell.target (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        ((h.app (laurent.op.obj (polynomial.op.obj X))).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        (z))))
  rw [permutation_lower_target, permutation_lower_target]
  exact congrArg (fun z => Cell.target ((coneFunctor.obj G).mapArrow.mapArrow.obj (square X)) n
        (Cell.lower (G.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n r (z)))
    (congrArg (fun k => k.map n z)
      (h.naturality (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).symm)

/-- Diagram naturality keeps the full original lower/upper cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:236"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_lower_upper (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (z : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) := by
  change (permutation G X).hom.map n (Cell.lower ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r (Cell.upper (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        ((h.app (polynomial.op.obj (polynomial.op.obj X))).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        (z))))
  rw [permutation_lower_upper, permutation_lower_upper]
  exact congrArg (fun z => Cell.upper ((coneFunctor.obj G).mapArrow.mapArrow.obj (square X)) n t
        (Cell.lower (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r (z)))
    (congrArg (fun k => k.map n z)
      (h.naturality (baseProductSwapMap (polynomialProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).symm)

/-- Diagram naturality keeps the full original lower/lower cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:259"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_lower_lower (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (z : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) := by
  change (permutation G X).hom.map n (Cell.lower ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r (Cell.lower (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        ((h.app (polynomial.op.obj (polynomial.op.obj X))).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        (z))))
  rw [permutation_lower_lower, permutation_lower_lower]
  exact congrArg (fun z => Cell.lower ((coneFunctor.obj G).mapArrow.mapArrow.obj (square X)) n t
        (Cell.lower (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n r (z)))
    (congrArg (fun k => k.map n z)
      (h.naturality (baseProductSwapMap (polynomialProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) X.unop).op).symm)

/-- Diagram naturality keeps the full original lower/overlap cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:282"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_lower_overlap (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t v :
        unitInterval)
    (z : (F.obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (z))) := by
  change (permutation G X).hom.map n (Cell.lower ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r (Cell.overlap (G.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        t v ((h.app (polynomial.op.obj X)).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        t v (z))))
  rw [permutation_lower_overlap, permutation_lower_overlap]
  all_goals rfl

/-- Diagram naturality keeps the full original overlap/target cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:302"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_overlap_target (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s :
        unitInterval)
    (z : (F.obj (laurent.op.obj X)).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.target
        (F.mapArrow.mapArrow.obj (square X)) n (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.target
        (F.mapArrow.mapArrow.obj (square X)) n (z))) := by
  change (permutation G X).hom.map n (Cell.overlap ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.target (G.mapArrow.mapArrow.obj (square X)) n ((h.app
        (laurent.op.obj X)).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.target (F.mapArrow.mapArrow.obj (square X)) n (z))))
  rw [permutation_overlap_target, permutation_overlap_target]
  all_goals rfl

/-- Diagram naturality keeps the full original overlap/upper cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:321"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_overlap_upper (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s t :
        unitInterval)
    (z : (F.obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.upper
        (F.mapArrow.mapArrow.obj (square X)) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.upper
        (F.mapArrow.mapArrow.obj (square X)) n t (z))) := by
  change (permutation G X).hom.map n (Cell.overlap ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.upper (G.mapArrow.mapArrow.obj (square X)) n t ((h.app
        (polynomial.op.obj X)).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.upper (F.mapArrow.mapArrow.obj (square X)) n t (z))))
  rw [permutation_overlap_upper, permutation_overlap_upper]
  all_goals rfl

/-- Diagram naturality keeps the full original overlap/lower cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:340"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_overlap_lower (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s t :
        unitInterval)
    (z : (F.obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.lower
        (F.mapArrow.mapArrow.obj (square X)) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.lower
        (F.mapArrow.mapArrow.obj (square X)) n t (z))) := by
  change (permutation G X).hom.map n (Cell.overlap ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.lower (G.mapArrow.mapArrow.obj (square X)) n t ((h.app
        (polynomial.op.obj X)).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.lower (F.mapArrow.mapArrow.obj (square X)) n t (z))))
  rw [permutation_overlap_lower, permutation_overlap_lower]
  all_goals rfl

/-- Diagram naturality keeps the full original overlap/overlap cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:359"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_overlap_overlap (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s t v :
        unitInterval)
    (z : (F.obj X).space n) :
    ((coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n t v (z))) := by
  change (permutation G X).hom.map n (Cell.overlap ((coneFunctor.obj G).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.overlap (G.mapArrow.mapArrow.obj (square X)) n t v ((h.app
        X).map n z))) =
    ((coneFunctor.map (coneFunctor.map h)).app X).map n
      ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.overlap (F.mapArrow.mapArrow.obj (square X)) n t v (z))))
  rw [permutation_overlap_overlap, permutation_overlap_overlap]
  all_goals rfl

/-- Every actual diagram transformation commutes with the entire geometric permutation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeNaturality.lean:378"
  "adaptation" "Original whole geometric naturality on all sixteen quotient cells."]
theorem permutation_diagram_naturality (h : F ⟶ G) (X : Scheme.{u}ᵒᵖ) :
    (coneFunctor.map (coneFunctor.map h)).app X ≫ (permutation G X).hom =
      (permutation F X).hom ≫ (coneFunctor.map (coneFunctor.map h)).app X := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  refine Cell.inductionOn ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n x
    ?_ ?_ ?_ ?_
  · intro y
    refine Cell.inductionOn (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n y
      ?_ ?_ ?_ ?_
    · intro z
      exact permutation_diagram_target_target h X n z
    · intro t z
      exact permutation_diagram_target_upper h X n t z
    · intro t z
      exact permutation_diagram_target_lower h X n t z
    · intro t v z
      exact permutation_diagram_target_overlap h X n t v z
  · intro r y
    refine Cell.inductionOn (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n y
      ?_ ?_ ?_ ?_
    · intro z
      exact permutation_diagram_upper_target h X n r z
    · intro t z
      exact permutation_diagram_upper_upper h X n r t z
    · intro t z
      exact permutation_diagram_upper_lower h X n r t z
    · intro t v z
      exact permutation_diagram_upper_overlap h X n r t v z
  · intro r y
    refine Cell.inductionOn (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n y
      ?_ ?_ ?_ ?_
    · intro z
      exact permutation_diagram_lower_target h X n r z
    · intro t z
      exact permutation_diagram_lower_upper h X n r t z
    · intro t z
      exact permutation_diagram_lower_lower h X n r t z
    · intro t v z
      exact permutation_diagram_lower_overlap h X n r t v z
  · intro r s y
    refine Cell.inductionOn (F.mapArrow.mapArrow.obj (square X)) n y
      ?_ ?_ ?_ ?_
    · intro z
      exact permutation_diagram_overlap_target h X n r s z
    · intro t z
      exact permutation_diagram_overlap_upper h X n r s t z
    · intro t z
      exact permutation_diagram_overlap_lower h X n r s t z
    · intro t v z
      exact permutation_diagram_overlap_overlap h X n r s t v z

end KTheory.Bass.GeometricConeInterchange

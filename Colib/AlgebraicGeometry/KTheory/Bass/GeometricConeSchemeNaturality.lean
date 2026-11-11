/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeNaturality
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
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})



/-- The original swap square retains its exact opposite direction under an arbitrary base map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:36"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem map_swap_naturality {S T : Scheme.{u}} (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ)
    (x : (F.obj ((baseProductFunctor q).op.obj ((baseProductFunctor p).op.obj X))).space n) :
    (F.map (baseProductSwapMap q p Y.unop).op).map n
      ((F.map ((baseProductFunctor q).op.map ((baseProductFunctor p).op.map g))).map n x) =
    (F.map ((baseProductFunctor p).op.map ((baseProductFunctor q).op.map g))).map n
      ((F.map (baseProductSwapMap q p X.unop).op).map n x) := by
  have hs : (baseProductFunctor q).op.map ((baseProductFunctor p).op.map g) ≫
      (baseProductSwapMap q p Y.unop).op =
    (baseProductSwapMap q p X.unop).op ≫
      (baseProductFunctor p).op.map ((baseProductFunctor q).op.map g) :=
    Quiver.Hom.unop_inj (baseProductSwapMap_naturality q p g.unop).symm
  have hm := congrArg F.map hs
  rw [F.map_comp, F.map_comp] at hm
  exact congrArg (fun k => k.map n x) hm

/-- Scheme naturality preserves the original target/target cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:53"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_target_target {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ)
    (z : (F.obj (laurent.op.obj (laurent.op.obj X))).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.target
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n (z))) := by
  change (permutation F Y).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n (Cell.target (F.mapArrow.mapArrow.obj (square (laurent.op.obj Y))) n
        ((F.map (laurent.op.map (laurent.op.map (g)))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.target (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n
        (z))))
  rw [permutation_target_target, permutation_target_target]
  exact congrArg (fun z => Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square Y)) n
        (Cell.target (F.mapArrow.mapArrow.obj (square (laurent.op.obj Y))) n (z)))
    (map_swap_naturality F (laurentProjection (.of (ULift.{u} ℤ))) (laurentProjection (.of
        (ULift.{u} ℤ))) g n z)

/-- Scheme naturality preserves the original target/upper cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:75"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_target_upper {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (t : unitInterval)
    (z : (F.obj (polynomial.op.obj (laurent.op.obj X))).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.upper
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.upper
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (z))) := by
  change (permutation F Y).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n (Cell.upper (F.mapArrow.mapArrow.obj (square (laurent.op.obj Y))) n t
        ((F.map (polynomial.op.map (laurent.op.map (g)))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.upper (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t
        (z))))
  rw [permutation_target_upper, permutation_target_upper]
  exact congrArg (fun z => Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square Y)) n t
        (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n (z)))
    (map_swap_naturality F (laurentProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of
        (ULift.{u} ℤ))) g n z)

/-- Scheme naturality preserves the original target/lower cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:97"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_target_lower {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (t : unitInterval)
    (z : (F.obj (polynomial.op.obj (laurent.op.obj X))).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.lower
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.lower
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t (z))) := by
  change (permutation F Y).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n (Cell.lower (F.mapArrow.mapArrow.obj (square (laurent.op.obj Y))) n t
        ((F.map (polynomial.op.map (laurent.op.map (g)))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.lower (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t
        (z))))
  rw [permutation_target_lower, permutation_target_lower]
  exact congrArg (fun z => Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square Y)) n t
        (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n (z)))
    (map_swap_naturality F (laurentProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of
        (ULift.{u} ℤ))) g n z)

/-- Scheme naturality preserves the original target/overlap cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:119"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_target_overlap {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (t v :
        unitInterval)
    (z : (F.obj (laurent.op.obj X)).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v (z))) := by
  change (permutation F Y).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n (Cell.overlap (F.mapArrow.mapArrow.obj (square (laurent.op.obj Y))) n t v
        ((F.map (laurent.op.map (g))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n (Cell.overlap (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))) n t v
        (z))))
  rw [permutation_target_overlap, permutation_target_overlap]
  all_goals rfl

/-- Scheme naturality preserves the original upper/target cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:139"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_upper_target {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (z : (F.obj (laurent.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (z))) := by
  change (permutation F Y).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n
        ((F.map (laurent.op.map (polynomial.op.map (g)))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        (z))))
  rw [permutation_upper_target, permutation_upper_target]
  exact congrArg (fun z => Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square Y)) n
        (Cell.upper (F.mapArrow.mapArrow.obj (square (laurent.op.obj Y))) n r (z)))
    (map_swap_naturality F (polynomialProjection (.of (ULift.{u} ℤ))) (laurentProjection (.of
        (ULift.{u} ℤ))) g n z)

/-- Scheme naturality preserves the original upper/upper cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:161"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_upper_upper {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r t : unitInterval)
    (z : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) := by
  change (permutation F Y).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n t
        ((F.map (polynomial.op.map (polynomial.op.map (g)))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        (z))))
  rw [permutation_upper_upper, permutation_upper_upper]
  exact congrArg (fun z => Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square Y)) n t
        (Cell.upper (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n r (z)))
    (map_swap_naturality F (polynomialProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of
        (ULift.{u} ℤ))) g n z)

/-- Scheme naturality preserves the original upper/lower cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:183"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_upper_lower {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r t : unitInterval)
    (z : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) := by
  change (permutation F Y).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n t
        ((F.map (polynomial.op.map (polynomial.op.map (g)))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        (z))))
  rw [permutation_upper_lower, permutation_upper_lower]
  exact congrArg (fun z => Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square Y)) n t
        (Cell.upper (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n r (z)))
    (map_swap_naturality F (polynomialProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of
        (ULift.{u} ℤ))) g n z)

/-- Scheme naturality preserves the original upper/overlap cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:205"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_upper_overlap {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r t v :
        unitInterval)
    (z : (F.obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (z))) := by
  change (permutation F Y).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n
        t v ((F.map (polynomial.op.map (g))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        t v (z))))
  rw [permutation_upper_overlap, permutation_upper_overlap]
  all_goals rfl

/-- Scheme naturality preserves the original lower/target cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:225"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_lower_target {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (z : (F.obj (laurent.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.target
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n (z))) := by
  change (permutation F Y).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n
        ((F.map (laurent.op.map (polynomial.op.map (g)))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.target (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        (z))))
  rw [permutation_lower_target, permutation_lower_target]
  exact congrArg (fun z => Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square Y)) n
        (Cell.lower (F.mapArrow.mapArrow.obj (square (laurent.op.obj Y))) n r (z)))
    (map_swap_naturality F (polynomialProjection (.of (ULift.{u} ℤ))) (laurentProjection (.of
        (ULift.{u} ℤ))) g n z)

/-- Scheme naturality preserves the original lower/upper cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:247"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_lower_upper {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r t : unitInterval)
    (z : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.upper
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) := by
  change (permutation F Y).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n t
        ((F.map (polynomial.op.map (polynomial.op.map (g)))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.upper (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        (z))))
  rw [permutation_lower_upper, permutation_lower_upper]
  exact congrArg (fun z => Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square Y)) n t
        (Cell.lower (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n r (z)))
    (map_swap_naturality F (polynomialProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of
        (ULift.{u} ℤ))) g n z)

/-- Scheme naturality preserves the original lower/lower cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:269"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_lower_lower {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r t : unitInterval)
    (z : (F.obj (polynomial.op.obj (polynomial.op.obj X))).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.lower
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t (z))) := by
  change (permutation F Y).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n t
        ((F.map (polynomial.op.map (polynomial.op.map (g)))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.lower (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t
        (z))))
  rw [permutation_lower_lower, permutation_lower_lower]
  exact congrArg (fun z => Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square Y)) n t
        (Cell.lower (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n r (z)))
    (map_swap_naturality F (polynomialProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of
        (ULift.{u} ℤ))) g n z)

/-- Scheme naturality preserves the original lower/overlap cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:291"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_lower_overlap {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r t v :
        unitInterval)
    (z : (F.obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r (Cell.overlap
        (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n t v (z))) := by
  change (permutation F Y).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square (polynomial.op.obj Y))) n
        t v ((F.map (polynomial.op.map (g))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r (Cell.overlap (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n
        t v (z))))
  rw [permutation_lower_overlap, permutation_lower_overlap]
  all_goals rfl

/-- Scheme naturality preserves the original overlap/target cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:311"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_overlap_target {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r s :
        unitInterval)
    (z : (F.obj (laurent.op.obj X)).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.target
        (F.mapArrow.mapArrow.obj (square X)) n (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.target
        (F.mapArrow.mapArrow.obj (square X)) n (z))) := by
  change (permutation F Y).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r s (Cell.target (F.mapArrow.mapArrow.obj (square Y)) n ((F.map
        (laurent.op.map (g))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.target (F.mapArrow.mapArrow.obj (square X)) n (z))))
  rw [permutation_overlap_target, permutation_overlap_target]
  all_goals rfl

/-- Scheme naturality preserves the original overlap/upper cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:330"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_overlap_upper {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r s t :
        unitInterval)
    (z : (F.obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.upper
        (F.mapArrow.mapArrow.obj (square X)) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.upper
        (F.mapArrow.mapArrow.obj (square X)) n t (z))) := by
  change (permutation F Y).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r s (Cell.upper (F.mapArrow.mapArrow.obj (square Y)) n t ((F.map
        (polynomial.op.map (g))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.upper (F.mapArrow.mapArrow.obj (square X)) n t (z))))
  rw [permutation_overlap_upper, permutation_overlap_upper]
  all_goals rfl

/-- Scheme naturality preserves the original overlap/lower cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:349"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_overlap_lower {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r s t :
        unitInterval)
    (z : (F.obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.lower
        (F.mapArrow.mapArrow.obj (square X)) n t (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.lower
        (F.mapArrow.mapArrow.obj (square X)) n t (z))) := by
  change (permutation F Y).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r s (Cell.lower (F.mapArrow.mapArrow.obj (square Y)) n t ((F.map
        (polynomial.op.map (g))).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.lower (F.mapArrow.mapArrow.obj (square X)) n t (z))))
  rw [permutation_overlap_lower, permutation_overlap_lower]
  all_goals rfl

/-- Scheme naturality preserves the original overlap/overlap cell and all its parameters. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:368"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_overlap_overlap {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r s t v :
        unitInterval)
    (z : (F.obj X).space n) :
    ((coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n t v (z))) =
    ((permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g).map n
      (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s (Cell.overlap
        (F.mapArrow.mapArrow.obj (square X)) n t v (z))) := by
  change (permutation F Y).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square Y)) n r s (Cell.overlap (F.mapArrow.mapArrow.obj (square Y)) n t v ((F.map
        (g)).map n z))) =
    ((coneFunctor.obj (coneFunctor.obj F)).map g).map n
      ((permutation F X).hom.map n (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj
        (square X)) n r s (Cell.overlap (F.mapArrow.mapArrow.obj (square X)) n t v (z))))
  rw [permutation_overlap_overlap, permutation_overlap_overlap]
  all_goals rfl

/-- Every original scheme map commutes with the full actual geometric permutation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:387"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
theorem permutation_scheme_naturality {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    (coneFunctor.obj (coneFunctor.obj F)).map g ≫ (permutation F Y).hom =
      (permutation F X).hom ≫ (coneFunctor.obj (coneFunctor.obj F)).map g := by
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
      exact permutation_scheme_target_target F g n z
    · intro t z
      exact permutation_scheme_target_upper F g n t z
    · intro t z
      exact permutation_scheme_target_lower F g n t z
    · intro t v z
      exact permutation_scheme_target_overlap F g n t v z
  · intro r y
    refine Cell.inductionOn (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n y
      ?_ ?_ ?_ ?_
    · intro z
      exact permutation_scheme_upper_target F g n r z
    · intro t z
      exact permutation_scheme_upper_upper F g n r t z
    · intro t z
      exact permutation_scheme_upper_lower F g n r t z
    · intro t v z
      exact permutation_scheme_upper_overlap F g n r t v z
  · intro r y
    refine Cell.inductionOn (F.mapArrow.mapArrow.obj (square (polynomial.op.obj X))) n y
      ?_ ?_ ?_ ?_
    · intro z
      exact permutation_scheme_lower_target F g n r z
    · intro t z
      exact permutation_scheme_lower_upper F g n r t z
    · intro t z
      exact permutation_scheme_lower_lower F g n r t z
    · intro t v z
      exact permutation_scheme_lower_overlap F g n r t v z
  · intro r s y
    refine Cell.inductionOn (F.mapArrow.mapArrow.obj (square X)) n y
      ?_ ?_ ?_ ?_
    · intro z
      exact permutation_scheme_overlap_target F g n r s z
    · intro t z
      exact permutation_scheme_overlap_upper F g n r s t z
    · intro t z
      exact permutation_scheme_overlap_lower F g n r s t z
    · intro t v z
      exact permutation_scheme_overlap_overlap F g n r s t v z

/-- The specified geometric permutation is an actual isomorphism of the original scheme diagrams. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:442"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
def permutationNatIso : coneFunctor.obj (coneFunctor.obj F) ≅
    coneFunctor.obj (coneFunctor.obj F) :=
  NatIso.ofComponents (permutation F) (permutation_scheme_naturality F)

/-- The same actual permutation is natural in every strict spectrum diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeSchemeNaturality.lean:447"
  "adaptation" "Original whole scheme naturality and the specified two-cone functor isomorphism."]
def permutationFunctorIso : coneFunctor.{u,w} ⋙ coneFunctor ≅ coneFunctor ⋙ coneFunctor :=
  NatIso.ofComponents permutationNatIso (fun h => by
    apply NatTrans.ext
    funext X
    exact permutation_diagram_naturality h X)

end KTheory.Bass.GeometricConeInterchange

namespace KTheory.Bass.GeometricConeInterchange

attribute [colib_tag "COL-0572"] permutationFunctorIso

end KTheory.Bass.GeometricConeInterchange

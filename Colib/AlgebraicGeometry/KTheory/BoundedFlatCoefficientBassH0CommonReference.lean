/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassChartBottomSourceReferences
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0Diagram

/-!
# The actual H₀ comparison at the common Laurent reference

Reanchoring changes only the stored comparison isomorphisms and preserves
the entire original H₀ diagram. Adapted from `BassH0CommonReference.lean`
in Quillen at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merge

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The original Laurent coefficient composite is the actual composite scheme map. -/
theorem laurent_composite : coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)) =
    BoundedFlatCoefficientBassChartBottomReferences.laurentComposite P u v := by
  rw [Functor.map_comp, coefficientMap_comp]

/-- The original polynomial coefficient composite has the analogous literal scheme equality. -/
theorem polynomial_composite : coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)) =
    coefficientMap P ((polynomialUnderFunctor R).map v) ≫
      coefficientMap P ((polynomialUnderFunctor R).map u) := by
  rw [Functor.map_comp, coefficientMap_comp]

/-- Native Laurent naturality identifies the H0 source with the old common geometric total. -/
theorem total : coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)) ≫
    laurentProjection P a =
      laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  rw [laurentProjection_naturality P (u ≫ v), coefficientMap_comp]

/-- The anchored source equality is induced only by the actual geometric total equation. -/
theorem reference_eq : (BoundedFlatCoefficientBassOverlap.commonReference P u v).hom.toFunctor =
    (BoundedFlatCoefficientBassH0Diagram.reference P (u ≫ v)).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback (total P u v).symm)

/-- Every old H0 node retains its actual functor and reference after canonical transport. -/
def nodes : Fin 31 → BoundedFlatCoefficientBassOverlap.Node P u v :=
  ModelSimplex.reanchorNodes (F₀ := BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (F₁ := BoundedFlatCoefficientBassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
    (BoundedFlatCoefficientBassH0Diagram.nodes P (u ≫ v))

/-- The original H0 simplex reanchored at the common Laurent reference via `reference_eq`. -/
def simplex := ModelSimplex.reanchorSimplex
  (F₀ := BoundedFlatCoefficientBassOverlap.commonReference P u v)
  (F₁ := BoundedFlatCoefficientBassH0Diagram.reference P (u ≫ v))
  (eqToIso (reference_eq P u v)) (BoundedFlatCoefficientBassH0Diagram.nodes P (u ≫ v))

/-- This reanchoring preserves the entire original H0 simplex, hence every existing native value. -/
theorem simplex_original : simplex P u v = BoundedFlatCoefficientBassH0Diagram.simplex P (u ≫ v) :=
  ModelSimplex.reanchorSimplex_eq (eqToIso (reference_eq P u v))
    (BoundedFlatCoefficientBassH0Diagram.nodes P (u ≫ v))

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merge

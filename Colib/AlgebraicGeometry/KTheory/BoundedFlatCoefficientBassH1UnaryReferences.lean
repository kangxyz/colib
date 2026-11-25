/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1UnaryComponents
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassOverlapReference

/-!
# The common Laurent reference of the two unary Bass composition components

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassH1References.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Both genuine unary components
share a reference without changing their underlying ordered diagrams.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1References

open BoundedFlatCoefficientBassOverlap

local notation "N" => boundedAboveFlatPerfectNormalizedPullback
local notation "NC" => boundedAboveFlatPerfectNormalizedPullbackCompIso

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The middle cylinder uses the original coefficient precomposition total. -/
theorem middle_total : (coefficientMap P ((laurentUnderFunctor R).map v) ≫
    laurentProjection P b) ≫ coefficientMap P u =
      laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  rw [laurentProjection_naturality P v, Category.assoc]

/-- The first cylinder has the same geometric total by Laurent projection naturality. -/
theorem first_total : coefficientMap P ((laurentUnderFunctor R).map v) ≫
    (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a) =
      laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  calc
    _ = coefficientMap P ((laurentUnderFunctor R).map v) ≫
        (laurentProjection P b ≫ coefficientMap P u) :=
      congrArg (fun f ↦ coefficientMap P ((laurentUnderFunctor R).map v) ≫ f)
        (laurentProjection_naturality P u)
    _ = (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b) ≫
        coefficientMap P u := (Category.assoc _ _ _).symm
    _ = _ := middle_total P u v

/-- Reanchor the actual first component using its normalized pullback comparison. -/
def firstIso : (commonReference P u v).hom.toFunctor ≅
    (BoundedFlatCoefficientBassH1Components.firstSource P u v).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg N (first_total P u v).symm) ≪≫
      NC (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a))
    AsSmall.up)

/-- Reanchor the actual middle component using its normalized pullback comparison. -/
def middleIso : (commonReference P u v).hom.toFunctor ≅
    (BoundedFlatCoefficientBassH1Components.middleSource P u v).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg N (middle_total P u v).symm) ≪≫
      NC (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
        (coefficientMap P u))
    AsSmall.up)

/-- The first component's dependent nodes with the common Laurent reference. -/
def firstNodes :=
  ModelSimplex.reanchorNodes (firstIso P u v)
    (BoundedFlatCoefficientBassH1Components.firstNodes P u v)

/-- The middle component's dependent nodes with the common Laurent reference. -/
def middleNodes :=
  ModelSimplex.reanchorNodes (middleIso P u v)
    (BoundedFlatCoefficientBassH1Components.middleNodes P u v)

/-- Reanchoring preserves the entire original first simplex. -/
theorem first_original : ModelSimplex.ofIsos (commonReference P u v)
    (fun i ↦ (firstNodes P u v i).1) (fun i ↦ (firstNodes P u v i).2) =
    BoundedFlatCoefficientBassH1Components.firstSimplex P u v :=
  ModelSimplex.ofIsos_change_reference (firstIso P u v) _ _

/-- Reanchoring preserves the entire original middle simplex. -/
theorem middle_original : ModelSimplex.ofIsos (commonReference P u v)
    (fun i ↦ (middleNodes P u v i).1) (fun i ↦ (middleNodes P u v i).2) =
    BoundedFlatCoefficientBassH1Components.middleSimplex P u v :=
  ModelSimplex.ofIsos_change_reference (middleIso P u v) _ _

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1References

/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.DedekindBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FlatCodimensionZero
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Integral components remain flat over the affine-line parameter

A flat scheme over the spectrum of a Dedekind domain has no vertical generic
component. Each actual reduced integral component is therefore flat over that
one-dimensional base. In the polynomial-family application the flat composite
is D → X × A1 → A1. This does not assert that a component is flat over X × A1.

The scheme, its native integral component, the inclusion, and the parameter
map are unchanged. No geometric-integrality assumption is imposed on a field
extension, and no support is selected in place of the whole family.

This is the native counterpart of the component-flatness input used by
motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
RelativeCurve/Endpoints/FiniteFlatCurveSpecialization.lean. The actual native
Dedekind-base theorem supplies the torsion-free/flat argument.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Stacks.Chow

/-- A genuine component of a flat scheme is flat over a Dedekind parameter.
No finiteness, reducedness, or integrality of the whole source is required. -/
theorem flat_integralComponentAt_to_dedekind
    {R : Type u} [CommRing R] [IsDedekindDomain R] {D : Scheme.{u}}
    (p : D ⟶ Spec (.of R)) [Flat p] (z : genericPoints D) :
    Flat ((integralComponentAt z.val).subschemeι ≫ p) := by
  letI : IsIntegral (integralComponentAt z.val).subscheme :=
    isIntegral_integralComponentAt z.val
  apply flat_of_genericPoint_map_eq
  have hpoint : (integralComponentAt z.val).subschemeι
      (genericPoint (integralComponentAt z.val).subscheme) = z.val :=
    genericPointOf_integralComponentAt z.val
  change p ((integralComponentAt z.val).subschemeι
    (genericPoint (integralComponentAt z.val).subscheme)) = _
  rw [hpoint]
  have hz := mem_genericPoints_of_flat p z.property
  simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hz

/-- Only flatness over the literal affine-line parameter is inherited by each
component. The finite-flat source projection to X × A1 is not inherited. -/
theorem flat_integralComponentAt_to_affineLine
    {k : Type u} [Field k] {D B : Scheme.{u}}
    (q : D ⟶ B) [Flat q] (t : B ⟶ Spec (.of (Polynomial k))) [Flat t]
    (z : genericPoints D) :
    Flat ((integralComponentAt z.val).subschemeι ≫ q ≫ t) := by
  simpa only [Category.assoc] using flat_integralComponentAt_to_dedekind (q ≫ t) z

end AlgebraicGeometry.Scheme.Hom

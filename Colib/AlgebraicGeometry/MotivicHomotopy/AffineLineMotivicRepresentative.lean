/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.AffineLineRepresentative
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Hypercohomology
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Colib.AlgebraicGeometry.Sites.Smooth.Injectives

import Colib.AlgebraicGeometry.MotivicCohomology.AffineLineInvariance
import Colib.AlgebraicGeometry.MotivicCohomology.Finite.AffineLineInvariance
import Colib.CategoryTheory.Sites.Simplicial.ParameterCylinderInvariance
import Colib.Util.References

/-!
# Affine-local representatives of the motivic complexes

The comparison from representable restrictions to all pointed cylinders
applies to the actual affine-line interval. Integral and finite motivic
coefficients over a perfect field therefore have the native cochain
representatives in the affine-line localization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers
open Stacks.Cohomology.FreeYonedaUnivLE

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

section SmoothSite

variable (S : Scheme.{u})

local notation "Cₛ" => SmoothSite S
local notation "Jₛ" => SmoothSite.nisnevichTopology S

set_option maxHeartbeats 600000 in
-- Comparing the smooth products and simplicial interval unfolds their universe lifts.
set_option backward.isDefEq.respectTransparency false in
/-- For the actual affine-line interval, invariance on the smooth
representables implies invariance on every pointed cylinder. -/
@[colib_tag "COL-1016"]
theorem bijective_reducedHypercohomology_map_affineLineCylinder
    [HasSheafify (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{d}
      (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]
    (K : CochainComplex (Sheaf Jₛ AddCommGrpCat.{u + 1}) ℤ)
    (h : ∀ (n : ℤ) (U : Cₛ), IsIso ((hypercohomologyPresheaf.{d, u + 1} Jₛ K n).map
      ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject S)).app U).op))
    (p : ℤ) (X : PointedSimplicialPresheaf.{u + 1} Cₛ) :
    Function.Bijective ((reducedHypercohomology.{d, u + 1} Cₛ Jₛ K p).map
      (cylinderProjection X (affineLineInterval S)).op) := by
  let V := SmoothSite.additiveGroupObject S
  apply bijective_reducedHypercohomology_map_cylinder.{d, u + 1, u, u + 1} Cₛ Jₛ V K _ p X
  intro n U
  let F := hypercohomologyPresheaf.{d, u + 1} Jₛ K n
  have : IsIso (F.map (SmoothSite.productFst U V).op) := h n U
  change IsIso (F.map (prod.fst : U ⨯ V ⟶ U).op)
  rw [← SmoothSite.categoricalProductIso_hom_fst U V, op_comp, F.map_comp]
  infer_instance

end SmoothSite

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Cₖ" => SmoothSite Sₖ
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ

/-- The affine-local cochain representative of the integral motivic complex. -/
abbrev motivicAffineLineRepresentative (p : ℤ) (q : ℕ) : AffineLineHomotopyCategory Sₖ :=
  affineLineCochainRepresentative Sₖ p (motivicSheafComplex k q)

/-- The affine-local cochain representative of the actual finite motivic cone. -/
abbrev motivicFiniteAffineLineRepresentative (p : ℤ) (q n : ℕ) :
    AffineLineHomotopyCategory Sₖ :=
  affineLineCochainRepresentative Sₖ p (motivicFiniteSheafComplex k q n)

variable [PerfectField k]
  [HasDerivedCategory.{d}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The integral affine-local representative computes the original reduced
motivic cohomology of every pointed simplicial presheaf over a perfect field. -/
@[no_expose, colib_tag "COL-1016", colib_ref "Voevodsky2003ReducedPowers"
  "Section 2, Theorem 2.1 and equation (2.9), pp. 3–5" "adaptation"
  "Affine-local representability using the actual integral cochain model"]
def motivicAffineLineRepresentativeHomEquiv (p : ℤ) (q : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) :
    ((toAffineLineHomotopyCategory Sₖ).obj X ⟶ motivicAffineLineRepresentative k p q) ≃
      (reducedHypercohomology.{d, u + 1} Cₖ Jₖ (motivicSheafComplex k q) p).obj (op X) :=
  affineLineCochainRepresentativeHomEquiv.{d} Sₖ p (motivicSheafComplex k q)
    (bijective_reducedHypercohomology_map_affineLineCylinder Sₖ (motivicSheafComplex k q)
      (fun n U ↦ motivicCohomologyPresheaf_isA1Invariant k n q U) p) X

/-- The finite affine-local representative computes the original reduced
hypercohomology of the finite coefficient cone over a perfect field. -/
@[no_expose, colib_tag "COL-1016"]
def motivicFiniteAffineLineRepresentativeHomEquiv (p : ℤ) (q n : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) :
    ((toAffineLineHomotopyCategory Sₖ).obj X ⟶ motivicFiniteAffineLineRepresentative k p q n) ≃
      (reducedHypercohomology.{d, u + 1} Cₖ Jₖ (motivicFiniteSheafComplex k q n) p).obj (op X) :=
  affineLineCochainRepresentativeHomEquiv.{d} Sₖ p (motivicFiniteSheafComplex k q n)
    (bijective_reducedHypercohomology_map_affineLineCylinder Sₖ (motivicFiniteSheafComplex k q n)
      (fun i U ↦ motivicFiniteCohomologyPresheaf_isA1Invariant k i q n U) p) X

end AlgebraicGeometry.MotivicHomotopy

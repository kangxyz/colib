/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitBottom
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0Native
public import Colib.KTheory.Waldhausen.Iterated.ModelReferenceReanchor

/-!
# The original H₀ face on the raw Bass identity

The native H₀ diagram at the coefficient identity is reanchored to the original unit
product. The 31 actual reference isomorphisms and their complete simplex are retained.
Adapted from the H₀ reanchoring of `CoefficientBassUnitHZeroNodes.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No signed chart collisions are asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitHZeroNodes

local notation "bassProjSource" => BoundedFlatCoefficientBassProjectionPath.source
local notation "hZeroNative" => BoundedFlatCoefficientBassH0Diagram.native
local notation "hZeroNodes" => BoundedFlatCoefficientBassH0Diagram.nodes
local notation "hZeroParameter" => BoundedFlatCoefficientBassH0Diagram.parameter
local notation "hZeroReference" => BoundedFlatCoefficientBassH0Diagram.reference
local notation "hZeroSimplex" => BoundedFlatCoefficientBassH0Diagram.simplex
local notation "bottomSrc" => BoundedFlatCoefficientBassUnitBottom.source
local notation "bottomToProj" => BoundedFlatCoefficientBassUnitBottom.sourceToProjection
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The actual projection and the H₀ reference at the coefficient identity have the same
normalized functor. -/
theorem h0SourceEq : (bassProjSource P a).hom.toFunctor =
    (hZeroReference P (𝟙 a)).hom.toFunctor := by
  have h : laurentPlus P a ≫ polynomialProjection P a =
      coefficientMap P ((laurentUnderFunctor R).map (𝟙 a)) ≫ laurentProjection P a := by
    rw [(laurentUnderFunctor R).map_id a,
      boundedAboveFlatCoefficientGeometricIdentity P ((laurentUnderFunctor R).obj a),
      Category.id_comp]
    exact laurentPlus_projection P a
  exact congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback h)

/-- The common identity anchor changes reference by the actual base identity and projection
isomorphism. -/
def h0SourceIso : (bottomSrc P a).hom.toFunctor ≅
    (hZeroReference P (𝟙 a)).hom.toFunctor :=
  bottomToProj P a ≪≫ eqToIso (h0SourceEq P a)

/-- All thirty-one actual H₀ vertices and full reanchored reference isomorphisms. -/
def h0Nodes (i : Fin 31) : Σ F : asSmallCategory (W (space (op P, a))) ⟶
    asSmallCategory (W (space (op P, (laurentUnderFunctor R).obj a))),
    (bottomSrc P a).hom.toFunctor ≅ F.hom.toFunctor :=
  ModelSimplex.reanchorNodes (F₀ := bottomSrc P a) (F₁ := hZeroReference P (𝟙 a))
    (h0SourceIso P a) (hZeroNodes P (𝟙 a)) i

/-- The full reanchored simplex for the original identity H₀ face. -/
def simplex : ModelSimplex (asSmallCategory (W (space (op P, a))))
    (asSmallCategory (W (space (op P, (laurentUnderFunctor R).obj a)))) 30 :=
  ModelSimplex.reanchorSimplex (F₀ := bottomSrc P a) (F₁ := hZeroReference P (𝟙 a))
    (h0SourceIso P a) (hZeroNodes P (𝟙 a))

/-- The original H₀ simplex survives its full common-reference transport. -/
theorem h0_family : simplex P a = hZeroSimplex P (𝟙 a) :=
  ModelSimplex.reanchorSimplex_eq (F₀ := bottomSrc P a) (F₁ := hZeroReference P (𝟙 a))
    (h0SourceIso P a) (hZeroNodes P (𝟙 a))

/-- The reanchored family retains the actual coefficient identity homotopy at every level,
including level zero, and with both original times independent. -/
theorem h0_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (hZeroParameter (s, t), x) =
      (boundedAboveFlatCoefficientBassComparisonHomotopy P (𝟙 a)).level n
        (s, HomotopyPushout.cylinder (K (polynomialProjection P a))
          (K (polynomialProjection P a)) n (t, x)) := by
  rw [h0_family]
  exact hZeroNative P (𝟙 a) n s t x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitHZeroNodes

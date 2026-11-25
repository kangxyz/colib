/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0Diagram
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceWhiskering

/-!
# The two unary H0 components of the original H1 diagram

Their full dependent nodes retain the normalized coefficient maps and the canonical isomorphisms.
Adapted from the source `BassH1Components.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS CommRingCat.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Components

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "NE" => boundedAboveFlatPerfectNormalizedPullback_exact
local notation "NZ" => boundedAboveFlatPerfectNormalizedPullback_obj_zero
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The normalized model map induced by the Laurent coefficient map of `v`. -/
abbrev laurentMap := asSmallCategoryMap _ _
  (NE (coefficientMap P ((laurentUnderFunctor R).map v))) (NZ _)

/-- The normalized model map induced by the coefficient scheme map of `u`. -/
abbrev coefficientMapModel := asSmallCategoryMap _ _ (NE (coefficientMap P u)) (NZ _)

/-- The H0 reference for `u` followed by the Laurent coefficient model map for `v`. -/
abbrev firstSource := BoundedFlatCoefficientBassH0Diagram.reference P u ≫ laurentMap P v

/-- The H0 nodes for `u` postcomposed with the Laurent coefficient map for `v`, including their
references. -/
def firstNodes (i : Fin 31) :
    Σ F : asSmallCategory (W (space (op P, a))) ⟶
      asSmallCategory (W (space (op P, (laurentUnderFunctor R).obj c))),
        (firstSource P u v).hom.toFunctor ≅ F.hom.toFunctor :=
  ⟨(BoundedFlatCoefficientBassH0Diagram.nodes P u i).1 ≫ laurentMap P v,
    isoWhiskerRight (BoundedFlatCoefficientBassH0Diagram.nodes P u i).2
      (laurentMap P v).hom.toFunctor⟩

/-- The first H1 component simplex, obtained by postcomposing the H0 simplex for `u`. -/
def firstSimplex := ModelSimplex.ofIsos (firstSource P u v)
  (fun i ↦ (firstNodes P u v i).1) (fun i ↦ (firstNodes P u v i).2)

/-- Postcompose the first component without changing the original simplex. -/
theorem first_simplex_original : firstSimplex P u v =
    (BoundedFlatCoefficientBassH0Diagram.simplex P u).postcomp (laurentMap P v) :=
  (ModelSimplex.ofIsos_postcomp _ _ _ _).symm

/-- The coefficient model map for `u` followed by the H0 reference for `v`. -/
abbrev middleSource := coefficientMapModel P u ≫ BoundedFlatCoefficientBassH0Diagram.reference P v

/-- The H0 nodes for `v` precomposed with the coefficient map for `u`, including their
references. -/
def middleNodes (i : Fin 31) :
    Σ F : asSmallCategory (W (space (op P, a))) ⟶
      asSmallCategory (W (space (op P, (laurentUnderFunctor R).obj c))),
        (middleSource P u v).hom.toFunctor ≅ F.hom.toFunctor :=
  ⟨coefficientMapModel P u ≫ (BoundedFlatCoefficientBassH0Diagram.nodes P v i).1,
    isoWhiskerLeft (coefficientMapModel P u).hom.toFunctor
      (BoundedFlatCoefficientBassH0Diagram.nodes P v i).2⟩

/-- The middle H1 component simplex, obtained by precomposing the H0 simplex for `v`. -/
def middleSimplex := ModelSimplex.ofIsos (middleSource P u v)
  (fun i ↦ (middleNodes P u v i).1) (fun i ↦ (middleNodes P u v i).2)

/-- Precompose the middle component without changing the original simplex. -/
theorem middle_simplex_original : middleSimplex P u v =
    (BoundedFlatCoefficientBassH0Diagram.simplex P v).precomp (coefficientMapModel P u) :=
  (ModelSimplex.ofIsos_precomp _ _ _ _).symm

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Components

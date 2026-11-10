/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Cylinder
public import Mathlib.Data.ZMod.Basic

/-! Consumers on the actual localized-unit coefficient groups and native complexes. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicTopology Opposite
open Polynomial
open Polynomial.BoundaryOneRationalFunctions
open scoped Simplicial

universe u

namespace BoundaryOneCylinderTest

variable (R : Type u) [CommRing R]

-- The complex in use is the literal native complex of the existing coordinate rings.
example (n : ℕ) :
    ((alternatingFaceMapComplex AddCommGrpCat).obj
      (AlgebraicSimplex.simplicialRing R ⋙ functor)).X n =
        AddCommGrpCat.of (Additive (group (AlgebraicSimplex.CoordinateRing R n))) := rfl

-- The original barycentric faces and their alternating signs are retained.
example (n : ℕ) :
    ((alternatingFaceMapComplex AddCommGrpCat).obj
      (AlgebraicSimplex.simplicialRing R ⋙ functor)).d (n + 1) n =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          functor.map ((AlgebraicSimplex.simplicialRing R).δ i) :=
  AlternatingFaceMapComplex.obj_d_eq _ n

-- All-degree vanishing has no additional acyclicity or exactness premise.
example (n : ℕ) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      (AlgebraicSimplex.simplicialRing R ⋙ functor)).homology n) :=
  isZero_homology_coordinateRings R n

-- Degree zero is included, not removed by an augmentation or truncation.
example :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      (AlgebraicSimplex.simplicialRing R ⋙ functor)).homology 0) :=
  isZero_homology_coordinateRings R 0

-- No nontriviality or domain hypothesis has slipped into the producer.
example (n : ℕ) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      (AlgebraicSimplex.simplicialRing PUnit ⋙ functor)).homology n) :=
  isZero_homology_coordinateRings PUnit n

-- A non-domain coefficient ring is also a literal instance of the same theorem.
example (n : ℕ) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      (AlgebraicSimplex.simplicialRing (ZMod 4) ⋙ functor)).homology n) :=
  isZero_homology_coordinateRings (ZMod 4) n

-- Every face, including face zero, vanishes on an actual normalized cycle.
example (n : ℕ)
    (x : ((normalizedMooreComplex AddCommGrpCat).obj
      (AlgebraicSimplex.simplicialRing R ⋙ functor)).X (n + 1))
    (hx : ((normalizedMooreComplex AddCommGrpCat).obj
      (AlgebraicSimplex.simplicialRing R ⋙ functor)).d (n + 1) n x = 0)
    (i : Fin (n + 2)) :
    functor.map ((AlgebraicSimplex.simplicialRing R).δ i)
      ((inclusionOfMooreComplexMap (AlgebraicSimplex.simplicialRing R ⋙ functor)).f
        (n + 1) x) = 0 :=
  SimplicialObject.normalized_cycle_faces _ n x hx i

-- Endpoints of the genuine ring-cylinder path, with no additivity premise.
example (n : ℕ) (x : Additive (group (AlgebraicSimplex.CoordinateRing R n))) :
    ((alternatingFaceMapComplex AddCommGrpCat).map
      (whiskerRight (NatTrans.op
        (CosimplicialObject.Cylinder.endpoint (algebraicSimplex R) 0)) ringPresheaf)).f n
      (cylinderPath (algebraicSimplex R) (AlgebraicSimplex.coordinate R 1 1) n x) = 0 :=
  cylinderPath_start (algebraicSimplex R) (AlgebraicSimplex.coordinate R 1 1)
    (algebraicSimplex_interval_zero R) n x

example (n : ℕ) (x : Additive (group (AlgebraicSimplex.CoordinateRing R n))) :
    ((alternatingFaceMapComplex AddCommGrpCat).map
      (whiskerRight (NatTrans.op
        (CosimplicialObject.Cylinder.endpoint (algebraicSimplex R) 1)) ringPresheaf)).f n
      (cylinderPath (algebraicSimplex R) (AlgebraicSimplex.coordinate R 1 1) n x) = x :=
  cylinderPath_end (algebraicSimplex R) (AlgebraicSimplex.coordinate R 1 1)
    (algebraicSimplex_interval_one R) n x

end BoundaryOneCylinderTest

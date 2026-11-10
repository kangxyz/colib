/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Cylinder
public import Colib.AlgebraicGeometry.Simplex.AffineRelativeComparison

/-!
# Boundary-one acyclicity on the actual affine relative simplex

Global sections of the actual simplex schemes are compared naturally with their
coordinate rings using `Scheme.ΓSpecIso`. The actual localized-unit cylinder
then proves vanishing in every chain degree, including zero. The affine relative
comparison keeps the original scheme pullbacks and every simplex operator.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Simplex/AffineBoundaryOneComplex.lean`
at revision a6805c4a87cdfd7717dd7a94039246a167f15380. Native alternating-face
complexes replace only the old generic wrappers, not the coefficient or geometry.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicTopology

universe u

namespace AlgebraicSimplex

open Polynomial.BoundaryOneRationalFunctions

variable (R : Type u) [CommRing R]

/-- Boundary-one functions on actual simplex schemes agree with actual coordinate-ring functions. -/
def schemeBoundaryOneSimplicialIso :
    (cosimplicialScheme R).op ⋙ Scheme.Γ ⋙ functor ≅ simplicialRing R ⋙ functor :=
  NatIso.ofComponents (fun n =>
    functor.mapIso (Scheme.ΓSpecIso (.of (CoordinateRing R n.unop.len)))) (by
      intro n m f
      change functor.map _ ≫ functor.map _ = functor.map _ ≫ functor.map _
      rw [← functor.map_comp, ← functor.map_comp]
      exact congrArg functor.map (Scheme.ΓSpecIso_naturality ((simplicialRing R).map f)))

/-- Every homology group of the genuine scheme coefficient complex vanishes. -/
theorem isZero_homology_schemeBoundaryOne (n : ℕ) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      ((cosimplicialScheme R).op ⋙ Scheme.Γ ⋙ functor)).homology n) := by
  let e := (alternatingFaceMapComplex AddCommGrpCat).mapIso (schemeBoundaryOneSimplicialIso R)
  exact (isZero_homology_coordinateRings R n).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.down ℕ) n).mapIso e)

variable {k : Type u} [CommRing k]

/-- The literal relative-product complex is acyclic, over any commutative coefficient rings. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Simplex/AffineBoundaryOneComplex.lean:53-59"
  "adaptation" "All-degree boundary-one vanishing on the original affine relative simplex"]
theorem isZero_homology_affineRelativeBoundaryOne (c : k →+* R) (n : ℕ) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      ((affineRelativeSimplex c).op ⋙ Scheme.Γ ⋙ functor)).homology n) := by
  let e := (alternatingFaceMapComplex AddCommGrpCat).mapIso
    (isoWhiskerRight (NatIso.op (affineRelativeSimplexIso c).symm) (Scheme.Γ ⋙ functor))
  exact (isZero_homology_schemeBoundaryOne R n).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.down ℕ) n).mapIso e)

end AlgebraicSimplex

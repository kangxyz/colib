/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Units.BoundaryOneComplex

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme AlgebraicSimplex Polynomial.BoundaryOneRationalFunctions
open scoped Simplicial

universe u

noncomputable section

namespace BoundaryOneGeometryTest

section Rings

variable {k R : Type u} [CommRing k] [CommRing R]

-- The producer keeps the literal pullback, including both original structure maps.
example (c : k →+* R) (n : ℕ) :
    (affineRelativeSimplex c).obj ⦋n⦌ =
      CategoryTheory.Limits.pullback (structureMap k n)
        (Spec.map (CommRingCat.ofHom c)) := rfl

-- All simplex operators, not just positive-degree faces, retain the old first projection.
example (c : k →+* R) {m n : SimplexCategory} (f : m ⟶ n) :
    (affineRelativeSimplex c).map f ≫
        pullback.fst (structureMap k n.len) (Spec.map (CommRingCat.ofHom c)) =
      pullback.fst (structureMap k m.len) (Spec.map (CommRingCat.ofHom c)) ≫
        (cosimplicialScheme k).map f :=
  relativeSimplexScheme_map_fst _ f

-- The affine pullback isomorphism retains every face and degeneracy, in the stated direction.
example (c : k →+* R) {m n : SimplexCategory} (f : m ⟶ n) :
    (affineRelativeSimplex c).map f ≫ (affineRelativeSimplexIso c).hom.app n =
      (affineRelativeSimplexIso c).hom.app m ≫ (cosimplicialScheme R).map f :=
  (affineRelativeSimplexIso c).hom.naturality f

-- The Gamma-Spec comparison applies the actual localized-unit functor to the canonical ring iso.
example (n : ℕ) :
    (schemeBoundaryOneSimplicialIso R).hom.app (op ⦋n⦌) =
      functor.map (Scheme.ΓSpecIso (.of (CoordinateRing R n))).hom := rfl

-- Both base and coefficient rings are arbitrary; no reducedness or flatness hypothesis is added.
example (c : k →+* R) (n : ℕ) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      ((affineRelativeSimplex c).op ⋙ Scheme.Γ ⋙ functor)).homology n) :=
  isZero_homology_affineRelativeBoundaryOne R c n

end Rings

-- The zero ring is included, in degree zero, on actual relative schemes.
example :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      ((affineRelativeSimplex (RingHom.id PUnit)).op ⋙ Scheme.Γ ⋙ functor)).homology 0) :=
  isZero_homology_affineRelativeBoundaryOne PUnit (RingHom.id PUnit) 0

section Fields

variable (k : Type u) [Field k]

-- The coefficient is the actual subgroup of localized units in global sections.
example (X : SmoothSite (Spec (.of k))) :
    (SmoothSite.boundaryOnePresheaf k).obj (op X) =
      AddCommGrpCat.of (Additive (group Γ(X.left, ⊤))) := rfl

-- The large coefficient is the native ULift, with the original restriction on elements.
example {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (x : (SmoothSite.boundaryOnePresheaf k).obj (op Y)) :
    (SmoothSite.largeBoundaryOnePresheaf k).map f.op (ULift.up x) =
      ULift.up ((SmoothSite.boundaryOnePresheaf k).map f.op x) := rfl

-- The chain terms are still the existing literal smooth-site relative products.
example (X : SmoothSite (Spec (.of k))) (n : ℕ) :
    (((singularChainsFunctor k).obj (SmoothSite.largeBoundaryOnePresheaf k)).X n).obj
        (op X) =
      (SmoothSite.largeBoundaryOnePresheaf k).obj
        (op (SmoothSite.product X (smoothSiteObj k n))) := rfl

-- The original ordered faces and integer signs are unchanged by the geometric comparison.
example (X : SmoothSite (Spec (.of k))) (n : ℕ) :
    (((singularChainsFunctor k).obj (SmoothSite.largeBoundaryOnePresheaf k)).d (n + 1) n).app
        (op X) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (SmoothSite.largeBoundaryOnePresheaf k).map
          (SmoothSite.productMap (𝟙 X) ((cosimplicialSmoothSite k).δ i)).op :=
  singularChainsFunctor_obj_d_app k (SmoothSite.largeBoundaryOnePresheaf k) n (op X)

-- The coordinate comparison is natural for degeneracies as well as for faces.
example (X : SmoothSite (Spec (.of k))) [IsAffine X.left] {n : ℕ} (i : Fin (n + 1)) :
    ((simplicialPresheaf k (SmoothSite.boundaryOnePresheaf k)).flip.obj (op X)).map
      (SimplexCategory.σ i).op ≫
        (SmoothSite.boundaryOneSimplicialAffineIso k X).hom.app (op ⦋n + 1⦌) =
      (SmoothSite.boundaryOneSimplicialAffineIso k X).hom.app (op ⦋n⦌) ≫
        (simplicialRing Γ(X.left, ⊤) ⋙ functor).map (SimplexCategory.σ i).op :=
  (SmoothSite.boundaryOneSimplicialAffineIso k X).hom.naturality (SimplexCategory.σ i).op

-- Native homology of actual evaluated ordinary chains vanishes, with no vanishing premise.
example (X : SmoothSite (Spec (.of k))) [IsAffine X.left] (n : ℕ) :
    IsZero (((((_root_.CategoryTheory.evaluation _
      AddCommGrpCat.{u + 1}).obj (op X)).mapHomologicalComplex
      (.down ℕ)).obj ((singularChainsFunctor k).obj
        (SmoothSite.largeBoundaryOnePresheaf k))).homology n) :=
  SmoothSite.isZero_homology_evaluate_largeBoundaryOne_affine k X n

-- Evaluation also detects actual presheaf homology, including degree zero on every affine.
example (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    IsZero ((((singularChainsFunctor k).obj
      (SmoothSite.largeBoundaryOnePresheaf k)).homology 0).obj (op X)) :=
  SmoothSite.isZero_homology_largeBoundaryOnePresheaf_affine k X 0

-- All homology sheaves vanish in the original large coefficient universe, over every field.
example (n : ℕ) :
    IsZero (((sheafifiedSingularChainsFunctor k
      (SmoothSite.nisnevichTopology (Spec (.of k)))).obj
        (SmoothSite.largeBoundaryOnePresheaf k)).homology n) :=
  SmoothSite.isZero_homology_boundaryOneSheafComplex k n

-- This is not a positive-degree-only theorem.
example : IsZero ((SmoothSite.boundaryOneSheafComplex k).homology 0) :=
  SmoothSite.isZero_homology_boundaryOneSheafComplex k 0

end Fields

end BoundaryOneGeometryTest

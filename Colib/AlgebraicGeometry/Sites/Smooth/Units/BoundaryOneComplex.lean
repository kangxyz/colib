/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.AffineBoundaryOneComplex
public import Colib.AlgebraicGeometry.Simplex.EndpointHomotopy
public import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.AffineHomology
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# Acyclicity of the actual boundary-one ordinary singular sheaf complex

The coefficient is the genuine boundary-one subgroup of localized units in
scheme global sections. The chain functor is the existing ordinary singular
chain functor on literal relative smooth-site products. The coefficient universe
is raised by Mathlib's actual `AddCommGrpCat.uliftFunctor`; its exactness and
the native evaluation comparison transport the affine all-degree result.

The genuine affine open covers detect zero Nisnevich sheafification. Thus all
homology sheaves vanish, including degree zero, over every field. The theorem
has no vanishing premise and no integral-source restriction. Identification
with a correspondence kernel and the weight-one quasi-isomorphism are separate
results and are not asserted here.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Units/BoundaryOneComplex.lean`
at revision a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicTopology

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

open _root_.AlgebraicSimplex Polynomial.BoundaryOneRationalFunctions

variable (k : Type u) [Field k]

/-- Actual global boundary-one rational functions with ordinary restriction. -/
def boundaryOnePresheaf : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (forgetScheme (Spec (.of k))).op ⋙ Scheme.Γ ⋙ functor

/-- The same actual coefficient in the original large motivic coefficient universe. -/
def largeBoundaryOnePresheaf : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  boundaryOnePresheaf k ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- Every actual ordinary simplex operator agrees with the affine coordinate-ring operator. -/
def boundaryOneSimplicialAffineIso (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    (simplicialPresheaf k (boundaryOnePresheaf k)).flip.obj (op X) ≅
      simplicialRing Γ(X.left, ⊤) ⋙ functor :=
  isoWhiskerRight (NatIso.op (productSimplexAffineIso X).symm) (Scheme.Γ ⋙ functor) ≪≫
    schemeBoundaryOneSimplicialIso Γ(X.left, ⊤)

/-- The actual unlifted ordinary simplex complex is acyclic on every affine smooth source. -/
theorem isZero_homology_boundaryOne_affine (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] (n : ℕ) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      ((simplicialPresheaf k (boundaryOnePresheaf k)).flip.obj (op X))).homology n) := by
  let e := (alternatingFaceMapComplex AddCommGrpCat).mapIso (boundaryOneSimplicialAffineIso k X)
  exact (isZero_homology_coordinateRings Γ(X.left, ⊤) n).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.down ℕ) n).mapIso e)

/-- The actual universe lift preserves affine acyclicity in every degree. -/
theorem isZero_homology_largeBoundaryOne_affine (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] (n : ℕ) :
    IsZero (((alternatingFaceMapComplex AddCommGrpCat).obj
      ((simplicialPresheaf k (largeBoundaryOnePresheaf k)).flip.obj (op X))).homology n) := by
  let S := (simplicialPresheaf k (boundaryOnePresheaf k)).flip.obj (op X)
  let K := (alternatingFaceMapComplex AddCommGrpCat).obj S
  let F := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let e := (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app S
  have h : IsZero (((F.mapHomologicalComplex (.down ℕ)).obj K).homology n) :=
    (F.map_isZero (isZero_homology_boundaryOne_affine k X n)).of_iso
      ((K.sc n).mapHomologyIso F)
  exact h.of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.down ℕ) n).mapIso e.symm)

/-- Evaluation of the existing large-coefficient ordinary singular chains is acyclic on affines. -/
theorem isZero_homology_evaluate_largeBoundaryOne_affine (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] (n : ℕ) :
    IsZero (((((_root_.CategoryTheory.evaluation _
      AddCommGrpCat.{u + 1}).obj (op X)).mapHomologicalComplex
      (.down ℕ)).obj ((singularChainsFunctor k).obj (largeBoundaryOnePresheaf k))).homology n) :=
  (isZero_homology_largeBoundaryOne_affine k X n).of_iso
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.down ℕ) n).mapIso
      (singularChainsEvaluationIso k (largeBoundaryOnePresheaf k) X))

/-- The presheaf homology itself vanishes on every affine source, in the large universe. -/
theorem isZero_homology_largeBoundaryOnePresheaf_affine (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] (n : ℕ) :
    IsZero ((((singularChainsFunctor k).obj (largeBoundaryOnePresheaf k)).homology n).obj
      (op X)) := by
  let K := (singularChainsFunctor k).obj (largeBoundaryOnePresheaf k)
  let E := (_root_.CategoryTheory.evaluation (SmoothSite (Spec (.of k)))ᵒᵖ
    AddCommGrpCat.{u + 1}).obj (op X)
  exact (isZero_homology_evaluate_largeBoundaryOne_affine k X n).of_iso
    ((K.sc n).mapHomologyIso E).symm

/-- The genuine ordinary boundary-one singular sheaf complex, with large coefficients. -/
def boundaryOneSheafComplex :
    ChainComplex (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) ℕ :=
  (sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
    (largeBoundaryOnePresheaf k)

/-- Every ordinary Nisnevich homology sheaf vanishes; degree zero is included. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Units/BoundaryOneComplex.lean:80-89"
  "adaptation" "All-degree vanishing using actual ordinary chains and affine open covers"]
theorem isZero_homology_boundaryOneSheafComplex (n : ℕ) :
    IsZero ((boundaryOneSheafComplex k).homology n) :=
  isZero_sheafified_homology_of_affine k
    ((singularChainsFunctor k).obj (largeBoundaryOnePresheaf k)) n
    (fun X _ => isZero_homology_largeBoundaryOnePresheaf_affine k X n)

end AlgebraicGeometry.Scheme.SmoothSite

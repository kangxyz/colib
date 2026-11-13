/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryFamily
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilySupport

/-!
# The actual signed principal polynomial correspondence

The literal polynomial `t*f+(1-t)` produces a native finite correspondence out of the
original polynomial cylinder. The whole boundary, properness and the quasi-affine retained
open produce finiteness; smooth relative dimension one produces component dominance.
Every signed order coefficient and every residue degree is retained by `PrincipalBoundary`.
This migrates the geometry of the archived `PrincipalFamily.lean`, without its old Finsupp
correspondence category. It does not claim the graph-endpoint/Tor cycle identities.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u

namespace Stacks.Chow.PrincipalPolynomialFamily

variable {R : Type u} [CommRing R] {C X Y V W B : Scheme.{u}}
  (p : X ⟶ Spec (.of R)) (t : Y ⟶ Spec (.of R))
  [IsAffine X] [IsSeparated t] [LocallyOfFiniteType t]
  (q : C ⟶ X) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W) [Nonempty B]
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
  (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
  [IsIntegral (parameterSpace (q ≫ p))] [IsNoetherian (parameterSpace (q ≫ p))]
  (g : V ⟶ Y) (hg : j ≫ q ≫ p = g ≫ t)

set_option backward.isDefEq.respectTransparency.types false in
/-- The signed principal family is a constructed native finite correspondence.
Neither finiteness nor component dominance is supplied as an extra cycle premise. -/
@[colib_tag "COL-1216",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/Picard/SmoothCurveLocalDimension.lean:254-258,300-309"
    "ingredient" "Closed points on the actual smooth curve fibres have stalk dimension one",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/FlatCodimensionZero.lean:183-185"
    "ingredient" "Flat maps preserve the actual generic points used in support dominance"]
def correspondence : finiteCorrespondences (projection p ≫ p) t := by
  have : IsAffineHom (projection p) := MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffine (parameterSpace p) := isAffine_of_isAffineHom (projection p)
  have : IsProper (lineMap p q) :=
    MorphismProperty.of_isPullback (lineMap_isPullback p q).flip inferInstance
  have : IsAffineHom (projection (j ≫ (q ≫ p))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : (parameterSpace (j ≫ (q ≫ p))).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom (projection (j ≫ (q ≫ p)))
  have : SmoothOfRelativeDimension 1 (lineMap (q ≫ p) j ≫ lineMap p q) :=
    MorphismProperty.of_isPullback
      ((lineMap_isPullback (q ≫ p) j).paste_horiz (lineMap_isPullback p q)).flip inferInstance
  let := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
  have hbase : lineMap (q ≫ p) j ≫ lineMap p q ≫ (projection p ≫ p) =
      (projection (j ≫ (q ≫ p)) ≫ g) ≫ t := by
    rw [lineMap_projection_assoc, lineMap_projection_assoc]
    simpa only [Category.assoc] using
      congrArg (fun h => projection (j ≫ (q ≫ p)) ≫ h) hg
  exact PrincipalBoundary.correspondence (projection p ≫ p) t (lineMap p q)
    (lineMap (q ≫ p) j) (ambientUnitOpen (q ≫ p) v f)
    (complement_subset_ambientUnitOpen (q ≫ p) j v b hcover f hf)
    (ambientUnitSection (q ≫ p) v f) (isUnit_ambientUnitSection (q ≫ p) v f)
    (projection (j ≫ (q ≫ p)) ≫ g) hbase

end Stacks.Chow.PrincipalPolynomialFamily

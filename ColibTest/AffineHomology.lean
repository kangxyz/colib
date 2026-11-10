module

import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.AffineHomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

universe u

noncomputable section

variable (k : Type u) [Field k]

-- Actual ordinary singular chains, with the correct large coefficient universe.
-- This tests only the detection bridge, not boundary-one coefficient acyclicity.
example (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (n : ℕ)
    (h : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left],
      IsZero ((((AlgebraicSimplex.singularChainsFunctor k).obj P).homology n).obj (op X))) :
    IsZero (((AlgebraicSimplex.sheafifiedSingularChainsFunctor k
      (SmoothSite.nisnevichTopology (Spec (.of k)))).obj P).homology n) :=
  SmoothSite.isZero_sheafified_homology_of_affine k _ n h

-- Degree zero is intentionally included; no positive-degree-only premise.
example (K : ChainComplex ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ)
    (h : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left],
      IsZero ((K.homology 0).obj (op X))) :
    IsZero ((((presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)).obj K).homology 0) :=
  SmoothSite.isZero_sheafified_homology_of_affine k K 0 h

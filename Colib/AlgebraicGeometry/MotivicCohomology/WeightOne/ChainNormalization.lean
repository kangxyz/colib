/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.SheafComparison
public import Colib.AlgebraicGeometry.Sites.Smooth.Units.UnitNormalization

/-!
# The actual degree-zero chain comparison

The sheafification unit and counit cancel before the canonical units projection
is applied. Pullback from the original smooth object then cancels that projection.
All maps are the existing geometric norm and the native units contraction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicSimplex

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The raw degree-zero component is the genuine norm followed by inverse simplex pullback. -/
@[reassoc] theorem rawChainComparison_zero :
    toSheafify (nisnevichTopology (Spec (.of k))) ((rawReducedSingular k).X 0) ≫
      (((weightOneSheafChainComparison k).f 0) ≫
        (HomologicalComplex.singleObjXSelf (.down ℕ) 0
          (largeUnitsSheaf (Spec (.of k)))).hom).hom =
    (((singularChainsFunctor k).map (reducedNorm k)).f 0) ≫
      (inv (unitsSimplexPullback k 0)).hom := by
  let J := nisnevichTopology (Spec (.of k))
  let ν := ((singularChainsFunctor k).map (reducedNorm k)).f 0
  let U := ((singularChainsFunctor k).obj (largeUnitsPresheaf (Spec (.of k)))).X 0
  let c := ((unitSheafifiedSingularIso k).hom.f 0).hom
  let p := ((unitSingularSheafHomotopyEquiv k).hom.f 0).hom
  let e := (HomologicalComplex.singleObjXSelf (.down ℕ) 0
    (largeUnitsSheaf (Spec (.of k)))).hom.hom
  have hu : toSheafify J U ≫ c = 𝟙 _ :=
    toSheafify_unitSheafifiedSingularIso_hom_f k 0
  have hp : p ≫ e = (inv (unitsSimplexPullback k 0)).hom :=
    congrArg (fun f => f.hom) (unitSingularSheafHomotopyEquiv_hom_f_zero_projection k)
  calc
    _ = (toSheafify J ((rawReducedSingular k).X 0) ≫ sheafifyMap J ν) ≫ c ≫ p ≫ e := by
      rfl
    _ = (ν ≫ toSheafify J U) ≫ c ≫ p ≫ e :=
      congrArg (fun η => η ≫ c ≫ p ≫ e) (toSheafify_naturality J ν).symm
    _ = ν ≫ (toSheafify J U ≫ c) ≫ p ≫ e := by simp only [Category.assoc]
    _ = ν ≫ (inv (unitsSimplexPullback k 0)).hom := by rw [hu, Category.id_comp, hp]

/-- For a section pulled from the original object, the chain comparison is its original norm. -/
@[reassoc] theorem rawChainComparison_zero_pullback (X : SmoothSite (Spec (.of k))) :
    (rawReducedTorus k).map (productFst X (smoothSiteObj k 0)).op ≫
      (toSheafify (nisnevichTopology (Spec (.of k)))
        ((rawReducedSingular k).X 0)).app (op X) ≫
      (((weightOneSheafChainComparison k).f 0) ≫
        (HomologicalComplex.singleObjXSelf (.down ℕ) 0
          (largeUnitsSheaf (Spec (.of k)))).hom).hom.app (op X) =
      (reducedNorm k).app (op X) := by
  have h := congrArg (fun η => η.app (op X)) (rawChainComparison_zero k)
  change (rawReducedTorus k).map (productFst X (smoothSiteObj k 0)).op ≫
    (toSheafify (nisnevichTopology (Spec (.of k))) ((rawReducedSingular k).X 0) ≫
      (((weightOneSheafChainComparison k).f 0) ≫
        (HomologicalComplex.singleObjXSelf (.down ℕ) 0
          (largeUnitsSheaf (Spec (.of k)))).hom).hom).app (op X) = _
  rw [h]
  change (rawReducedTorus k).map (productFst X (smoothSiteObj k 0)).op ≫
    (reducedNorm k).app (op (product X (smoothSiteObj k 0))) ≫
      (inv (unitsSimplexPullback k 0)).hom.app (op X) = _
  rw [← Category.assoc, (reducedNorm k).naturality (productFst X (smoothSiteObj k 0)).op]
  change (reducedNorm k).app (op X) ≫
    (unitsSimplexPullback k 0).hom.app (op X) ≫
      (inv (unitsSimplexPullback k 0)).hom.app (op X) = _
  have hi : (unitsSimplexPullback k 0).hom.app (op X) ≫
      (inv (unitsSimplexPullback k 0)).hom.app (op X) =
        𝟙 ((largeUnitsPresheaf (Spec (.of k))).obj (op X)) :=
    congrArg (fun η => η.hom.app (op X)) (IsIso.hom_inv_id (unitsSimplexPullback k 0))
  rw [hi, Category.comp_id]

end AlgebraicGeometry.MotivicCohomology.WeightOne

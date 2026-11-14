/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.SingleSourceTransport
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallKummer
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.SourceSections

/-! # Canonical source transport through the actual full-small functor -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE Stacks.Cohomology.Corepresented
universe u wN wE wS
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{wE}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : SmoothSite (Spec (.of k)))
variable [HasDerivedCategory.{wS} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Full-small restriction transports the actual canonical shifted-single source map. -/
lemma fullSmallUnits_sourceMap (V : EtaleSeparatedFiniteType X.left)
    (h : (freeYoneda.{u + 1} (SmoothSite.etaleTopology (Spec (.of k)))).obj
        ((toSmoothSite X).obj V) ⟶ largeUnitsEtaleSheaf (Spec (.of k))) :
    fullSmallDerivedHomMap X V (weightOneEtaleUnitsComplex k) 1
        ((DerivedCategory.singleFunctor _ 0).map h ≫
          (derivedSingleNegOneCancelIso (largeUnitsEtaleSheaf (Spec (.of k)))).inv) ≫
      (DerivedCategory.Q.map (fullSmallEtaleUnitsComplexIso k X).hom)⟦(1 : ℤ)⟧' ≫
      (derivedSingleNegOneCancelIso (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)).hom =
    (DerivedCategory.singleFunctor _ 0).map
      (fullSmallSourceMap X V ≫ (fullSmallEtaleRestrict X).map h ≫
        (fullSmallUnitsIso X).hom) := by
  have h₁ := derivedSourceTransport_singleMap_cancel (fullSmallEtaleRestrict X)
    ((freeYoneda.{u + 1} (SmoothSite.etaleTopology (Spec (.of k)))).obj ((toSmoothSite X).obj V))
    (largeUnitsEtaleSheaf (Spec (.of k)))
    ((freeYoneda.{u + 1} X.left.smallEtaleTopology).obj ((toSmallEtale X.left).obj V))
    (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)
    (fullSmallSourceMap X V) (fullSmallUnitsIso X) h
  have hi : fullSmallEtaleUnitsComplexIso k X =
      CochainComplex.finiteCoefficients.shiftedSingleFunctorIso (fullSmallEtaleRestrict X)
        (largeUnitsEtaleSheaf (Spec (.of k)))
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left) (fullSmallUnitsIso X) := rfl
  rw [hi]
  simpa only [fullSmallDerivedHomMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    weightOneEtaleUnitsComplex, Category.assoc] using h₁

end AlgebraicGeometry.MotivicCohomology.WeightOne

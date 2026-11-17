module
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterA1Descent
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.DerivedForgetInvariance

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
universe u w w'
variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) (b : ℤ) (hb : K.IsLE b)
    (h : ∀ q, ((DerivedCategory.homologyFunctor
      (SheafWithTransfers.{u + 1} k) q).obj K).IsStrictA1Invariant) (p : ℤ) :
    ((DerivedCategory.homologyFunctor (PresheafWithTransfers.{u + 1} k) p).obj
      ((SheafWithTransfers.forgetDerivedFunctor k).obj K)).IsA1Invariant :=
  SheafWithTransfers.isA1Invariant_homology_forgetDerived_of_strict k K b hb h p

#print axioms SheafWithTransfers.isIso_transferExt_projection_of_strict
#print axioms SheafWithTransfers.isIso_transferDerivedHomPresheaf_projection_of_strict
#print axioms SheafWithTransfers.isA1Invariant_homology_forgetDerived_of_strict
#print axioms MotivicHomotopy.isA1Invariant_homology_parameterSectionsDerived_of_strict
#check @MotivicHomotopy.isA1Invariant_homology_parameterSectionsDerived_of_strict

#print axioms MotivicHomotopy.bijective_precomp_singularUnit_to_parameterSections_of_strict
#check @MotivicHomotopy.bijective_precomp_singularUnit_to_parameterSections_of_strict

#print axioms MotivicHomotopy.bijective_precomp_singularPresheafToEffectiveUnit_of_strict
#check @MotivicHomotopy.bijective_precomp_singularPresheafToEffectiveUnit_of_strict

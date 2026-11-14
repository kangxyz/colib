/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Hypercohomology
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Map

/-! # The original base-field integral reduction is actual derived postcomposition -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme SmoothSite CochainComplex.finiteCoefficients
open Stacks.Cohomology.FreeYonedaUnivLE
universe w u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance : ((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
    (op (base (Spec (.of k))))).Additive :=
  Functor.additive_of_iso (coyonedaIsoSheafSections.{u + 1}
    (nisnevichTopology (Spec (.of k))) (base (Spec (.of k))))

/-- The original evaluation/cone iso preserves the actual integral cochain map. -/
lemma motivicFiniteBaseComplexIso_integral (q n : ℕ) :
    (((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
      (op (base (Spec (.of k))))).mapHomologicalComplex (.up ℤ)).map
        (integral (motivicSheafComplex k q) n) ≫ (motivicFiniteBaseComplexIso k q n).hom =
      integral (motivicBaseComplex k q) n := by
  have h := mapIso_integral
    ((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
      (op (base (Spec (.of k))))) (motivicSheafComplex k q) n
  rw [mapIso_eq _ _ _ (by
    rw [Functor.map_nsmul]
    exact congrArg (fun f => n • f) (CategoryTheory.Functor.map_id _ _))] at h
  exact h

variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The pre-existing field reduction is postcomposition by the original finite integral map. -/
lemma motivicBaseIntegralReduction_eq_postcompose (p : ℤ) (q n : ℕ)
    (x : motivicCohomology k p q (base (Spec (.of k)))) :
    motivicBaseIntegralReduction k p q n x =
      x ≫ (DerivedCategory.Q.map (integral (motivicSheafComplex k q) n))⟦p⟧' := by
  apply (motivicFiniteBaseConeComparison k p q n).injective
  rw [motivicBaseIntegralReduction_comparison]
  change integralHomology (motivicBaseComplex k q) n p (motivicBaseEvaluationComparison k p q x) =
    HomologicalComplex.homologyMap (motivicFiniteBaseComplexIso k q n).hom p
      (hypercohomologyBaseFieldAddEquiv k (motivicFiniteSheafComplex k q n) p
        (x ≫ (DerivedCategory.Q.map (integral (motivicSheafComplex k q) n))⟦p⟧'))
  erw [hypercohomologyBaseFieldAddEquiv_naturality k
    (integral (motivicSheafComplex k q) n) p x]
  have h := congrArg (fun f => HomologicalComplex.homologyMap f p)
    (motivicFiniteBaseComplexIso_integral k q n)
  rw [HomologicalComplex.homologyMap_comp] at h
  exact (ConcreteCategory.congr_hom h
    (motivicBaseEvaluationComparison k p q x)).symm

end AlgebraicGeometry.PresheafWithTransfers

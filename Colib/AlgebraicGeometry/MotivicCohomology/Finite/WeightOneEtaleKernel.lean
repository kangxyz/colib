/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneSheafComparison
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.EtaleChangeOfTopology
public import Colib.AlgebraicGeometry.Sites.Smooth.Units.KummerLocalSurjectivity
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Kernel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Actual weight-one étale kernel comparison -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
attribute [instance] CategoryTheory.sheafIsAbelian

universe u
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]

/-- The actual shifted single étale units complex, not a substitute motivic object. -/
def weightOneEtaleUnitsComplex :=
  ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (largeUnitsEtaleSheaf (Spec (.of k))))⟦(-1 : ℤ)⟧

/-- Native shift, single and sheafification-counit comparisons. -/
def weightOneUnitsChangeOfTopologyIso :
    ((nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj (weightOneUnitsComplex k) ≅
      weightOneEtaleUnitsComplex k :=
  (((nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).commShiftIso (-1 : ℤ)).app _ ≪≫
  (shiftFunctor _ (-1 : ℤ)).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex
      (nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
        AddCommGrpCat.{u + 1}) (.up ℤ) 0).app _ ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso
        (nisnevichToEtaleLargeUnitsIso (Spec (.of k))))

/-- Étale image of the already proved geometric weight-one comparison. -/
def weightOneEtaleSheafComparison :
    motivicEtaleSheafComplex k 1 ⟶ weightOneEtaleUnitsComplex k :=
  ((nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).map (weightOneSheafComparison k) ≫
    (weightOneUnitsChangeOfTopologyIso k).hom

instance weightOneEtaleSheafComparison_quasiIso :
    QuasiIso (weightOneEtaleSheafComparison k) := by
  let : QuasiIso (weightOneSheafComparison k) := weightOneSheafComparison_quasiIso k
  have h : QuasiIso
      (((nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).map
          (weightOneSheafComparison k)) := inferInstance
  have h' : QuasiIso (weightOneUnitsChangeOfTopologyIso k).hom := inferInstance
  unfold weightOneEtaleSheafComparison
  infer_instance

/-- Starts at the original mapped finite motivic cone, using canonical mapIso. -/
def weightOneFiniteEtaleSheafComparison (n : ℕ) :
    motivicFiniteEtaleSheafComplex k 1 n ⟶
      CochainComplex.finiteCoefficients (weightOneEtaleUnitsComplex k) n :=
  (motivicFiniteEtaleSheafComplexIso k 1 n).hom ≫
    CochainComplex.finiteCoefficients.map n (weightOneEtaleSheafComparison k)

theorem weightOneFiniteEtaleSheafComparison_quasiIso (n : ℕ) :
    QuasiIso (weightOneFiniteEtaleSheafComparison k n) := by
  have := CochainComplex.finiteCoefficients.quasiIso_map n
    (weightOneEtaleSheafComparison k)
  unfold weightOneFiniteEtaleSheafComparison
  infer_instance

variable [HasDerivedCategory
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- D(Ab) comparison on the smooth étale site. Its codomain is the
literal multiplication kernel on actual global units. This is not yet the
small-site rootsOfUnityModule, nor a D(ZMod n) equivalence. -/
@[colib_tag "COL-1231", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:39-132" "ingredient"
  "Exact sheafification of weight one, followed by the actual Kummer kernel"]
def weightOneFiniteEtaleKernelIso (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.obj (motivicFiniteEtaleSheafComplex k 1 n) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (kernel (n • 𝟙 (largeUnitsEtaleSheaf (Spec (.of k)))))) := by
  have := weightOneFiniteEtaleSheafComparison_quasiIso k n
  letI := Kummer.largeUnitsEtaleSheaf_nsmul_epi (Spec (.of k)) n hn hunit
  exact asIso (DerivedCategory.Q.map (weightOneFiniteEtaleSheafComparison k n)) ≪≫
    CochainComplex.finiteCoefficients.kernelSingleFiniteIso
      (largeUnitsEtaleSheaf (Spec (.of k))) n

end AlgebraicGeometry.MotivicCohomology.WeightOne

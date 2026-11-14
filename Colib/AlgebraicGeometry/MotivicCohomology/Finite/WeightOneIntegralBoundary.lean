/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneEtaleCohomology
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralKummerComparison
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.DerivedRestrictionAtBaseNaturality
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.DerivedNaturality
public import Colib.Algebra.Homology.DerivedCategory.KernelBoundaryDegreeOne
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerSourceSections

/-! # Original finite weight-one comparison on an integral reduction -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType CochainComplex.finiteCoefficients
open Stacks.Cohomology.FreeYonedaUnivLE Stacks.Cohomology.Corepresented
universe u wN wE wS wH
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : SmoothSite (Spec (.of k)))
variable [HasDerivedCategory.{wE}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{wS} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{wH} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

set_option maxHeartbeats 1600000 in
-- Comparing the original coefficient functors requires reducing several exact transports.
private lemma weightOneFiniteFullSmallRootsIso_integral_boundary
    (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    (DerivedCategory.Q.map
      (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map
        (((nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1}).mapHomologicalComplex
          (.up ℤ)).map (integral (motivicSheafComplex k 1) n))))⟦(1 : ℤ)⟧' ≫
      (weightOneFiniteFullSmallRootsIso k X n hn hunit).hom⟦(1 : ℤ)⟧' =
    (DerivedCategory.Q.map
      (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map
        (weightOneEtaleSheafComparison k)))⟦(1 : ℤ)⟧' ≫
      (DerivedCategory.Q.map (fullSmallEtaleUnitsComplexIso k X).hom)⟦(1 : ℤ)⟧' ≫
      (derivedSingleNegOneCancelIso (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)).hom ≫
      (Stacks.Kummer.kummerSequence_shortExact.{u, 0} X.left hn
        (by simpa only [map_natCast] using hunit.map X.hom.appTop.hom)).extClass.hom := by
  let hu : IsUnit (n : Γ(X.left, ⊤)) := by
    simpa only [map_natCast] using hunit.map X.hom.appTop.hom
  let : Epi (n • 𝟙 (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)) :=
    Stacks.Kummer.epi_powMap X.left hn hu
  let A := DerivedCategory.Q.map
    (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map
      (((nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (.up ℤ)).map (integral (motivicSheafComplex k 1) n)))
  let B := DerivedCategory.Q.map (weightOneFiniteFullSmallKummerComparison k X n)
  let C := (Stacks.Kummer.kummerSingleFiniteIso X.left n hn hu).hom
  let R := (weightOneFiniteFullSmallRootsIso k X n hn hunit).hom
  let D := DerivedCategory.Q.map
    (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map
      (weightOneEtaleSheafComparison k))
  let E := DerivedCategory.Q.map (fullSmallEtaleUnitsComplexIso k X).hom
  let I := DerivedCategory.Q.map (integral
    (((HomologicalComplex.single _ (.up ℤ) 0).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left))⟦(-1 : ℤ)⟧) n)
  let c := (derivedSingleNegOneCancelIso
    (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)).hom
  let e := (Stacks.Kummer.kummerSequence_shortExact.{u, 0} X.left hn hu).extClass.hom
  have hr : B ≫ C = R :=
    weightOneFiniteFullSmallRootsIso_eq_kummer k X n hn hunit
  have hc0 : A ≫ B = D ≫ E ≫ I := by
    dsimp only [A, B, D, E, I]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun f => DerivedCategory.Q.map f)
        (weightOneFiniteFullSmallKummerComparison_integral k X n)
  have h0 : A ≫ R = (D ≫ E) ≫ (I ≫ C) := by
    calc
      A ≫ R = A ≫ (B ≫ C) := congrArg (fun f => A ≫ f) hr.symm
      _ = (A ≫ B) ≫ C := (Category.assoc A B C).symm
      _ = (D ≫ E ≫ I) ≫ C := congrArg (fun f => f ≫ C) hc0
      _ = (D ≫ E) ≫ (I ≫ C) := by simp only [Category.assoc]
  have hb : (I ≫ C)⟦(1 : ℤ)⟧' = c ≫ e :=
    integral_kernelSingleFiniteIso_extClass_one
      (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left) n
  change A⟦(1 : ℤ)⟧' ≫ R⟦(1 : ℤ)⟧' =
    D⟦(1 : ℤ)⟧' ≫ E⟦(1 : ℤ)⟧' ≫ c ≫ e
  calc
    A⟦(1 : ℤ)⟧' ≫ R⟦(1 : ℤ)⟧' = (A ≫ R)⟦(1 : ℤ)⟧' :=
      (Functor.map_comp (shiftFunctor _ (1 : ℤ)) A R).symm
    _ = ((D ≫ E) ≫ (I ≫ C))⟦(1 : ℤ)⟧' :=
      congrArg (fun f => f⟦(1 : ℤ)⟧') h0
    _ = (D ≫ E)⟦(1 : ℤ)⟧' ≫ (I ≫ C)⟦(1 : ℤ)⟧' :=
      Functor.map_comp (shiftFunctor _ (1 : ℤ)) (D ≫ E) (I ≫ C)
    _ = (D ≫ E)⟦(1 : ℤ)⟧' ≫ (c ≫ e) :=
      congrArg (fun f => (D ≫ E)⟦(1 : ℤ)⟧' ≫ f) hb
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

variable [HasDerivedCategory.{wN}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

set_option maxHeartbeats 1600000 in
-- Comparing the original coefficient functors requires reducing several exact transports.
/-- The original finite comparison of an integral class is the original small-site boundary. -/
lemma weightOneFiniteEtaleCohomologyMap_integral_boundary
    (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : Γ(Spec (.of k), ⊤)))
    (x : motivicCohomology k 1 1 X) :
    weightOneFiniteEtaleCohomologyMap k X 1 n hn hunit
      (x ≫ (DerivedCategory.Q.map (integral (motivicSheafComplex k 1) n))⟦(1 : ℤ)⟧') =
    terminalDerivedHomAddEquivH.{wH, wS, u + 1} X.left.smallEtaleTopology
      (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left n) (Scheme.Etale.mk (𝟙 X.left))
      (MorphismProperty.Over.mkIdTerminal _ _) 1
      (fullSmallDerivedHomMapAtBase X (motivicEtaleSheafComplex k 1) 1
          (nisnevichToEtaleDerivedHomMap (Spec (.of k)) X (motivicSheafComplex k 1) 1 x) ≫
        (DerivedCategory.Q.map
          (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map
            (weightOneEtaleSheafComparison k)))⟦(1 : ℤ)⟧' ≫
        (DerivedCategory.Q.map (fullSmallEtaleUnitsComplexIso k X).hom)⟦(1 : ℤ)⟧' ≫
        (derivedSingleNegOneCancelIso (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)).hom ≫
        (Stacks.Kummer.kummerSequence_shortExact.{u, 0} X.left hn
          (by simpa only [map_natCast] using hunit.map X.hom.appTop.hom)).extClass.hom) := by
  let hu : IsUnit (n : Γ(X.left, ⊤)) := by
    simpa only [map_natCast] using hunit.map X.hom.appTop.hom
  let : Epi (n • 𝟙 (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)) :=
    Stacks.Kummer.epi_powMap X.left hn hu
  change terminalDerivedHomAddEquivH.{wH, wS, u + 1} X.left.smallEtaleTopology
    (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left n) (Scheme.Etale.mk (𝟙 X.left))
    (MorphismProperty.Over.mkIdTerminal _ _) 1
    (fullSmallDerivedHomMapAtBase X (motivicFiniteEtaleSheafComplex k 1 n) 1
      (nisnevichToEtaleDerivedHomMap (Spec (.of k)) X (motivicFiniteSheafComplex k 1 n) 1
        (x ≫ (DerivedCategory.Q.map (integral (motivicSheafComplex k 1) n))⟦(1 : ℤ)⟧')) ≫
      (weightOneFiniteFullSmallRootsIso k X n hn hunit).hom⟦(1 : ℤ)⟧') = _
  congr 1
  rw [nisnevichToEtaleDerivedHomMap_coefficient, fullSmallDerivedHomMapAtBase_coefficient]
  simpa only [Category.assoc, motivicEtaleSheafComplex,
    DerivedCategory.Q_obj_single_obj] using congrArg
    (fun f => fullSmallDerivedHomMapAtBase X (motivicEtaleSheafComplex k 1) 1
      (nisnevichToEtaleDerivedHomMap (Spec (.of k)) X
        (motivicSheafComplex k 1) 1 x) ≫ f)
    (weightOneFiniteFullSmallRootsIso_integral_boundary k X n hn hunit)

end AlgebraicGeometry.MotivicCohomology.WeightOne

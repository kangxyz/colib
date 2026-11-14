/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallRoots
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.KernelFunctor
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerConeBoundary
/-! # The original full-small weight-one comparison is the native Kummer cone comparison -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
attribute [instance] CategoryTheory.sheafIsAbelian
universe u w w'
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]


variable (X : SmoothSite (Spec (.of k)))
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'}
  (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CochainComplex.finiteCoefficients

/-- The original single and shift transports of the actual full-small units iso. -/
def fullSmallEtaleUnitsComplexIso :
    ((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).obj
      (weightOneEtaleUnitsComplex k) ≅
    (((HomologicalComplex.single _ (.up ℤ) 0).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left))⟦(-1 : ℤ)⟧) :=
  shiftedSingleFunctorIso (fullSmallEtaleRestrict X)
    (largeUnitsEtaleSheaf (Spec (.of k)))
    (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left) (fullSmallUnitsIso X)

/-- Restrict the existing weight-one chain map and use the native finite-cone transport. -/
def weightOneFiniteFullSmallKummerComparison (n : ℕ) :
    ((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).obj
      (motivicFiniteEtaleSheafComplex k 1 n) ⟶
    CochainComplex.finiteCoefficients
      (((HomologicalComplex.single _ (.up ℤ) 0).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left))⟦(-1 : ℤ)⟧) n :=
  ((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map
      (weightOneFiniteEtaleSheafComparison k n) ≫
    (mapIso (fullSmallEtaleRestrict X) (weightOneEtaleUnitsComplex k) n).hom ≫
    map n (fullSmallEtaleUnitsComplexIso k X).hom

/-- The existing full-small roots iso is precisely the original small-site Kummer cone iso.
This is an equality with the pre-existing comparison, not a replacement definition. -/
lemma weightOneFiniteFullSmallRootsIso_eq_kummer (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.map (weightOneFiniteFullSmallKummerComparison k X n) ≫
      (Stacks.Kummer.kummerSingleFiniteIso X.left n hn
        (by simpa only [map_natCast] using hunit.map X.hom.appTop.hom)).hom =
      (weightOneFiniteFullSmallRootsIso k X n hn hunit).hom := by
  let hu : IsUnit (n : Γ(X.left, ⊤)) := by
    simpa only [map_natCast] using hunit.map X.hom.appTop.hom
  let : Epi (n • 𝟙 (largeUnitsEtaleSheaf (Spec (.of k)))) :=
    Kummer.largeUnitsEtaleSheaf_nsmul_epi (Spec (.of k)) n hn hunit
  let : Epi (n • 𝟙 (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)) :=
    Stacks.Kummer.epi_powMap X.left hn hu
  dsimp only [weightOneFiniteFullSmallKummerComparison, Stacks.Kummer.kummerSingleFiniteIso]
  rw [DerivedCategory.Q.map_comp, Category.assoc]
  erw [kernelSingleFiniteIso_map (fullSmallEtaleRestrict X)
    (largeUnitsEtaleSheaf (Spec (.of k)))
    (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left) (fullSmallUnitsIso X) n]
  dsimp only [weightOneFiniteFullSmallRootsIso, weightOneFiniteEtaleKernelIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  erw [(fullSmallEtaleRestrict X).mapDerivedCategoryFactors.inv.naturality_assoc]
  simp only [kernelSingleFunctorIso, Iso.trans_hom, Functor.mapIso_hom,
    DerivedCategory.Q.map_comp]
  rfl

end AlgebraicGeometry.MotivicCohomology.WeightOne

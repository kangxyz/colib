/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallRoots
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.FullSmallEtaleComparison
public import Colib.CategoryTheory.Sites.TerminalCohomologyUnivLE
/-! # Actual full-small weight-one roots-of-unity comparison -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
attribute [instance] CategoryTheory.sheafIsAbelian
universe u w w' wH wN
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


variable [HasExt.{wH} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
open Stacks.Cohomology.FreeYonedaUnivLE

set_option maxHeartbeats 800000 in
-- Elaborating the composed equivalence crosses several universe-lifted sheaf categories.
/-- Actual full-small finite weight-one hypercohomology is ordinary μ_n cohomology.
This is target identification; it does not claim the Nisnevich comparison is an iso. -/
@[colib_tag "COL-1231", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/CategoryTheory/Sites/GlobalSections/CohomologyAtTheTerminalObject.lean"
  "ingredient" "Terminal derived-Hom to ordinary Sheaf.H after the actual mu_n identification"]
def weightOneFullSmallCohomologyEquivH (p n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    motivicFiniteFullSmallEtaleCohomology k X (p : ℤ) 1 n ≃+
      Sheaf.H.{wH} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left n) p := by
  let e := (shiftFunctor _ (p : ℤ)).mapIso
    (weightOneFiniteFullSmallRootsIso k X n hn hunit)
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 X.left)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  refine AddEquiv.trans ?_
    (terminalDerivedHomAddEquivH.{wH, w', u + 1} X.left.smallEtaleTopology
      (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left n)
      (Scheme.Etale.mk (𝟙 X.left)) hT p)
  exact
    { toFun := fun f => f ≫ e.hom
      invFun := fun f => f ≫ e.inv
      left_inv := fun f => by simp [Category.assoc]
      right_inv := fun f => by simp [Category.assoc]
      map_add' := fun f g => by simp [Preadditive.add_comp] }

variable [HasDerivedCategory.{wN}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original finite motivic comparison now lands in ordinary étale μ_n cohomology.
It remains an additive map, not an asserted comparison isomorphism. -/
@[colib_tag "COL-1231", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/CategoryTheory/Sites/GlobalSections/CohomologyAtTheTerminalObject.lean"
  "ingredient" "Terminal derived-Hom to ordinary Sheaf.H after the actual mu_n identification"]
def weightOneFiniteEtaleCohomologyMap (p n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    motivicFiniteCohomology k (p : ℤ) 1 n X →+
      Sheaf.H.{wH} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left n) p :=
  (weightOneFullSmallCohomologyEquivH k X p n hn hunit).toAddMonoidHom.comp
    (motivicFiniteFullSmallEtaleCohomologyComparison k X (p : ℤ) 1 n)

end AlgebraicGeometry.MotivicCohomology.WeightOne

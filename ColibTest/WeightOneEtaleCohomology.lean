/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneEtaleCohomology
/-! # Actual full-small weight-one roots-of-unity comparison -/
noncomputable section
set_option linter.hashCommand false
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


variable [HasDerivedCategory.{wN}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
#print axioms weightOneFullSmallCohomologyEquivH
#print axioms weightOneFiniteEtaleCohomologyMap
example : motivicFiniteFullSmallEtaleCohomology k X 0 1 1 ≃+
    Sheaf.H.{wH} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left 1) 0 :=
  weightOneFullSmallCohomologyEquivH k X 0 1 (by decide) (by simp)
example (hunit : IsUnit (6 : Γ(Spec (.of k), ⊤))) :
    motivicFiniteCohomology k 2 1 6 X →+
      Sheaf.H.{wH} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left 6) 2 :=
  weightOneFiniteEtaleCohomologyMap k X 2 6 (by decide) hunit
example : QuasiIso (weightOneFiniteEtaleSheafComparison k 0) :=
  weightOneFiniteEtaleSheafComparison_quasiIso k 0
end AlgebraicGeometry.MotivicCohomology.WeightOne

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for decl in [``AlgebraicGeometry.MotivicCohomology.WeightOne.weightOneFiniteEtaleKernelIso,
      ``AlgebraicGeometry.MotivicCohomology.WeightOne.weightOneFiniteFullSmallRootsIso,
      ``AlgebraicGeometry.MotivicCohomology.WeightOne.weightOneFullSmallCohomologyEquivH,
      ``AlgebraicGeometry.MotivicCohomology.WeightOne.weightOneFiniteEtaleCohomologyMap] do
    unless (Colib.Library.bindings env).any (fun b =>
        b.id == "COL-1231" && b.declName == decl) do
      throwError "Missing COL-1231 binding for {decl}"
    for ax in ← collectAxioms decl do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "Unexpected axiom {ax} in {decl}"
    let refs := (Colib.Library.citations env).filter (fun c => c.declName == decl)
    unless refs.size == 1 do
      throwError "Expected exactly one reference for {decl}, got {refs.size}"
    for c in refs do
      logInfo m!"COL1231_REF|{c.source}|{c.locator}"
  let decl := ``AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.fullSmallRootsOfUnityIso
  let refs := (Colib.Library.citations env).filter (fun c => c.declName == decl)
  unless refs.size == 1 do
    throwError "Expected one roots-of-unity definition reference, got {refs.size}"
  for c in refs do
    logInfo m!"ROOTS_REF|{c.source}|{c.locator}"

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import all Colib.AlgebraicGeometry.PresheavesWithTransfers.TorsionSubpresheaf
import all Colib.AlgebraicGeometry.PresheavesWithTransfers.TorsionNeighborhoodReduction
import all Colib.AlgebraicGeometry.PresheavesWithTransfers.TorsionRigidityReduction
import all Colib.AlgebraicGeometry.PresheavesWithTransfers.EtaleRigidityTorsion
import all Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodMono
meta import Batteries.Tactic.Lint

/-! # Tests for sectionwise torsion rigidity without a common exponent -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
universe u
variable {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)

example (X : Cor k) (x : sections (torsionSubpresheaf P 0) X) : (0 : ℕ) • x = 0 :=
  torsionSubpresheaf_nsmul P 0 X x

example (X : Cor k) (x : sections (torsionSubpresheaf P 1) X) : x = 0 := by
  simpa only [one_nsmul] using torsionSubpresheaf_nsmul P 1 X x

example (X : Cor k) (x : sections (torsionSubpresheaf P 6) X) : (6 : ℕ) • x = 0 :=
  torsionSubpresheaf_nsmul P 6 X x

-- The annihilator is chosen after the object and section; there is no common exponent.
example (hA : IsA1Invariant P)
    (hT : ∀ (V : SmoothSite (Spec (.of k)))
      (x : sections P ((Cor.graphFunctor k).obj V)),
      ∃ m : ℕ, 0 < m ∧ IsUnit (m : k) ∧ m • x = 0) :
    let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)
    IsIso ((fullSmallEtaleAdjunction (SmoothSite.base (Spec (.of k)))).counit.app F) :=
  isIso_fullSmallEtale_sheafification_counit_of_primeToCharacteristicTorsion P hA hT

-- The original fixed-exponent assumption remains a sufficient special case.
example (n : ℕ) (hn : IsUnit ((n + 1 : ℕ) : k))
    (h : ∀ (V : SmoothSite (Spec (.of k)))
      (x : sections P ((Cor.graphFunctor k).obj V)), (n + 1) • x = 0) :
    IsPrimeToCharacteristicTorsion P := by
  intro V x
  exact ⟨n + 1, Nat.succ_pos n, hn, h V x⟩

run_meta do
  for decl in [``torsionSections,
    ``torsionFunctor,
    ``torsionSubpresheaf,
    ``torsionInclusion,
    ``torsionSubpresheaf_nsmul,
    ``isA1Invariant_torsionSubpresheaf,
    ``IsPrimeToCharacteristicTorsion,
    ``exists_torsionSubpresheaf_neighborhood_lift,
    ``torsionInclusion_neighborhood_injective,
    ``isIso_counit_of_sectionwiseTorsion_of_fixedExponentRigidity,
    ``isIso_structuralPullback_of_torsionSubpresheaf_pullbacks,
    ``isIso_fullSmallEtale_sheafification_counit_of_primeToCharacteristicTorsion,
    ``AlgebraicGeometry.Scheme.SmoothSite.etaleNeighborhoodValue_map_injective] do
    for linter in [Batteries.Tactic.Lint.docBlame, Batteries.Tactic.Lint.unusedArguments,
        Batteries.Tactic.Lint.simpNF] do
      match ← linter.test decl with
      | none => pure ()
      | some msg => Lean.logError m!"{decl}: {msg}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (fun ax =>
        [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      Lean.logError m!"Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"CHECKED {decl}; AXIOMS {axioms}"
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let decl := ``isIso_fullSmallEtale_sheafification_counit_of_primeToCharacteristicTorsion
  unless (Colib.Library.bindings env).any (fun b => b.id == "COL-1222" && b.declName == decl) do
    throwError "Missing general torsion rigidity binding"
  let cs := (Colib.Library.citations env).filter (fun c => c.declName == decl)
  unless cs.size == 1 do throwError "Expected exact MVW 7.20/7.21 reference"
  for c in cs do
    IO.println <| "CITATION_JSON:" ++ (Json.mkObj [
      ("source", toJson c.source), ("locator", toJson c.locator)]).compress

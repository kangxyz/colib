/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.SheafComparison
public import Colib.CategoryTheory.Sites.Hypercohomology.Shift
public import Colib.CategoryTheory.Sites.Hypercohomology.SheafComparison

/-!
# Weight-one motivic cohomology on every smooth scheme

The genuine comparison with the original signed shift is localized in the
existing unbounded derived category. Ordinary cohomology is the native Stacks
free-Yoneda Ext presheaf, retaining an independent Ext universe. No affineness,
connectedness, perfectness, characteristic or presumed quasi-isomorphism enters
these endpoints.

Adapted from Motivic/Cohomology/WeightOne/Hypercohomology.lean at revision
a6805c4a87cdfd7717dd7a94039246a167f15380, lines 35-80.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite

universe w w' u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open Stacks.Cohomology.FreeYonedaUnivLE

namespace HypercohomologyComparison

universe t vC uC

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max vC t}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max vC t})]

/-- Apply hypercohomology to a quasi-isomorphism with an abstract site and complexes. -/
def quasiIsoHypercohomologyPresheafIso
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{max vC t}) ℤ}
    (f : K ⟶ L) [QuasiIso f] (p : ℤ) :
    hypercohomologyPresheaf.{w, t} J K p ≅ hypercohomologyPresheaf.{w, t} J L p :=
  asIso ((hypercohomologyPresheafFunctor.{w, t} J p).map f)

/-- Signed shift and degree transport over the same abstract site. -/
def hypercohomologyPredShiftIso
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max vC t}) ℤ) (p : ℤ) :
    hypercohomologyPresheaf.{w, t} J (K⟦(-1 : ℤ)⟧) p ≅
      hypercohomologyPresheaf.{w, t} J K (p - 1) :=
  hypercohomologyShiftPresheafIso.{w, t} J K (-1) p ≪≫
    eqToIso (congrArg (fun i => hypercohomologyPresheaf.{w, t} J K i)
      (show (-1 : ℤ) + p = p - 1 by omega))

/-- Compose the map iso and signed transport before specializing either the site or complexes. -/
def quasiIsoHypercohomologyPredShiftIso
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{max vC t}) ℤ}
    (f : K ⟶ L⟦(-1 : ℤ)⟧) [QuasiIso f] (p : ℤ) :
    hypercohomologyPresheaf.{w, t} J K p ≅ hypercohomologyPresheaf.{w, t} J L (p - 1) :=
  quasiIsoHypercohomologyPresheafIso.{w, t} J f p ≪≫
    hypercohomologyPredShiftIso.{w, t} J L p

end HypercohomologyComparison

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w}
    (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original weight-one cohomology presheaf is shifted genuine Gm hypercohomology. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightOne/Hypercohomology.lean:33-49" "adaptation"
  "All integer degrees and every smooth scheme using the actual signed comparison",
  colib_tag "COL-0404"]
def weightOneHypercohomologyPresheafIso (p : ℤ) :
    motivicCohomologyPresheaf.{w, u} k p 1 ≅
      hypercohomologyPresheaf.{w, u + 1}
        (nisnevichTopology (Spec (.of k)))
        ((CochainComplex.singleFunctor _ 0).obj (largeUnitsSheaf (Spec (.of k))))
        (p - 1) := by
  exact HypercohomologyComparison.quasiIsoHypercohomologyPredShiftIso.{w, u + 1}
    (nisnevichTopology (Spec (.of k))) (weightOneSheafComparison k) p

/-- Every actual restriction of smooth schemes commutes with the comparison. -/
@[colib_tag "COL-0404", reassoc] theorem weightOneHypercohomologyPresheafIso_naturality
    (p : ℤ) {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (motivicCohomologyPresheaf.{w, u} k p 1).map f.op ≫
        (weightOneHypercohomologyPresheafIso k p).hom.app (op X) =
      (weightOneHypercohomologyPresheafIso k p).hom.app (op Y) ≫
        (hypercohomologyPresheaf.{w, u + 1} (nisnevichTopology (Spec (.of k)))
          ((CochainComplex.singleFunctor _ 0).obj (largeUnitsSheaf (Spec (.of k))))
          (p - 1)).map f.op :=
  (weightOneHypercohomologyPresheafIso k p).hom.naturality f.op

/-- H^(n+1,1)(X) is native ordinary H^n_Nis(X,Gm), with its independent Ext universe. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightOne/Hypercohomology.lean:51-74" "adaptation"
  "Every smooth source and nonnegative sheaf degree, preserving independent Ext universe",
  colib_tag "COL-0404"]
def weightOneSheafCohomologyEquiv
    [HasExt.{w'} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    motivicCohomology.{w, u} k ((n : ℤ) + 1) 1 X ≃+
      (cohomologyPresheaf.{w', u + 1} (largeUnitsSheaf (Spec (.of k))) n).obj (op X) := by
  let J := nisnevichTopology (Spec (.of k))
  let K := (CochainComplex.singleFunctor _ 0).obj (largeUnitsSheaf (Spec (.of k)))
  have e : AddCommGrpCat.of (motivicCohomology.{w, u} k ((n : ℤ) + 1) 1 X) ≅
      (hypercohomologyPresheaf.{w, u + 1} J K (n : ℤ)).obj (op X) := by
    let h : (n : ℤ) + 1 - 1 = n := by omega
    exact (weightOneHypercohomologyPresheafIso k ((n : ℤ) + 1)).app (op X) ≪≫
      eqToIso (congrArg (fun i =>
        (hypercohomologyPresheaf.{w, u + 1} J K i).obj (op X)) h)
  exact e.addCommGroupIsoToAddEquiv.trans
    (singleHypercohomologyEquivCohomology.{w', w, u + 1}
      J (largeUnitsSheaf (Spec (.of k))) n X)

end AlgebraicGeometry.MotivicCohomology.WeightOne

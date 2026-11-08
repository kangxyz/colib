/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Koszul.ScalarExtensionComparison
public import StacksFrontier.RingTheory.Koszul.TorComparison.QuotientTor
public import StacksFrontier.RingTheory.Tor.FlatExtendScalarsFirst
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# Free Koszul projection formula for an arbitrary ring map

The coefficient module has its genuine target-ring action. Native scalar extension
of the free Koszul complex, native coefficient identification, and native tensor
projection formula compare the two actual complexes, retaining the original ring
map and the literal mapped list. No flatness, regularity, finite length or
comparison equality is an input. In particular finite image maps may be nonflat.

The imported scalar-extension comparison uses the pinned native exterior-power
base-change map and differential identity; this file does not reconstruct them.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Koszul

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {r : ℕ}

/-- Native projection formula with the coefficient on the right. This uses
only braiding and the native left-coefficient projection formula. -/
def tensorRightExtendRestrictIso (M : ModuleCat.{u} S) :
    ModuleCat.extendScalars (algebraMap R S) ⋙ tensorRight M ⋙
      ModuleCat.restrictScalars (algebraMap R S) ≅
        tensorRight ((ModuleCat.restrictScalars (algebraMap R S)).obj M) :=
  Functor.isoWhiskerLeft (ModuleCat.extendScalars (algebraMap R S))
    (Functor.isoWhiskerRight (BraidedCategory.tensorLeftIsoTensorRight M).symm
      (ModuleCat.restrictScalars (algebraMap R S))) ≪≫
    Stacks.TorFlatExtendScalars.tensorExtendScalarsIso (algebraMap R S) M ≪≫
      BraidedCategory.tensorLeftIsoTensorRight _

/-- Free Koszul projection formula for the actual coefficient module, along
any ring map. In particular the finite image map need not be flat. -/
def seqComplexTensorRestrictScalarsIso (f : Fin r → R) (M : ModuleCat.{u} S) :
    seqComplexTensor f ((ModuleCat.restrictScalars (algebraMap R S)).obj M) ≅
      ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.down ℕ)).obj
        (seqComplexTensor (fun j => algebraMap R S (f j)) M) :=
  (tensoringRightSeqComplexIso f
    ((ModuleCat.restrictScalars (algebraMap R S)).obj M)).symm ≪≫
    ((NatIso.mapHomologicalComplex (tensorRightExtendRestrictIso (R := R) M)
      (.down ℕ)).app (seqComplex f)).symm ≪≫
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (.down ℕ)).mapIso
      (((tensorRight M).mapHomologicalComplex (.down ℕ)).mapIso
        (seqComplexBaseChangeIso (A := S) f) ≪≫
          tensoringRightSeqComplexIso (fun j => algebraMap R S (f j)) M)

/-- Homology of the coefficient projection formula, retaining its original
restricted scalar action. No new action on an abstract Tor group is postulated. -/
def homologySeqComplexTensorRestrictScalarsIso
    (f : Fin r → R) (M : ModuleCat.{u} S) (n : ℕ) :
    (seqComplexTensor f ((ModuleCat.restrictScalars (algebraMap R S)).obj M)).homology n ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((seqComplexTensor (fun j => algebraMap R S (f j)) M).homology n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (seqComplexTensorRestrictScalarsIso f M) ≪≫
      (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
        (ModuleCat.restrictScalars (algebraMap R S)) (.down ℕ) n).app
          (seqComplexTensor (fun j => algebraMap R S (f j)) M)

end Koszul

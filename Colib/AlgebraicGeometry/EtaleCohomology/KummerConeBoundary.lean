/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.KernelBoundary
public import Colib.CategoryTheory.Sites.TerminalCohomologyBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.CohomologySequence

/-! # The actual small-etale Kummer boundary and the signed finite cone -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex CochainComplex.finiteCoefficients

universe w w' u

namespace Stacks.Kummer

variable (X : Scheme.{u})
variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The signed finite cone of the actual small-site units identifies with existing μ_n. -/
def kummerSingleFiniteIso (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : Γ(X, ⊤))) :
    DerivedCategory.Q.obj (finiteCoefficients
      (((HomologicalComplex.single _ (.up ℤ) 0).obj
        (multiplicativeSheaf.{u, 0} X))⟦(-1 : ℤ)⟧) n) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (rootsOfUnitySheaf.{u, 0} X n)) := by
  letI : Epi (n • 𝟙 (multiplicativeSheaf.{u, 0} X)) := epi_powMap X hn hunit
  exact kernelSingleFiniteIso (multiplicativeSheaf.{u, 0} X) n

/-- The original coefficient reduction is precisely the shifted original Kummer Ext class. -/
lemma integral_kummerSingleFiniteIso (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(X, ⊤))) :
    DerivedCategory.Q.map (integral
      (((HomologicalComplex.single _ (.up ℤ) 0).obj
        (multiplicativeSheaf.{u, 0} X))⟦(-1 : ℤ)⟧) n) ≫
      (kummerSingleFiniteIso X n hn hunit).hom =
    (DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (multiplicativeSheaf.{u, 0} X)) ≫
      ((kummerSequence_shortExact.{u, 0} X hn hunit).extClass.hom)⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).hom.app
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
          (rootsOfUnitySheaf.{u, 0} X n))) := by
  let : Epi (n • 𝟙 (multiplicativeSheaf.{u, 0} X)) := epi_powMap X hn hunit
  exact integral_kernelSingleFiniteIso_extClass (multiplicativeSheaf.{u, 0} X) n

end Stacks.Kummer

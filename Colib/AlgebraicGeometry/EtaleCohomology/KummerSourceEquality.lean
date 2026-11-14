/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.KummerSourceSections

/-!
# Source-equality input for the ordinary Kummer boundary

This packages the existing terminal Kummer theorem.
It introduces no motivic comparison or rigidity hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.FreeYonedaUnivLE
universe w w' u
namespace Stacks.Kummer
variable (X : Scheme.{u})
variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Evaluating the original terminal boundary on the canonical representative of a unit. -/
lemma terminalDerived_unitKummerClass_sections (n : ℕ) (hn : n ≠ 0)
    (hu : IsUnit (n : Γ(X, ⊤))) (s : Additive (Γ(X, ⊤))ˣ) :
    terminalDerivedHomAddEquivH.{w, w', u + 1} X.smallEtaleTopology
      (rootsOfUnitySheaf.{u, 0} X n) (Scheme.Etale.mk (𝟙 X))
      (MorphismProperty.Over.mkIdTerminal _ _) 1
      ((DerivedCategory.singleFunctor _ 0).map
        ((sectionsEquiv.{u + 1} (Scheme.Etale.mk (𝟙 X))
          (multiplicativeSheaf.{u, 0} X)).symm (ULift.up s)) ≫
        (kummerSequence_shortExact.{u, 0} X hn hu).extClass.hom) =
    unitKummerClass.{w, u, 0} X hn hu s := by
  simpa only [Equiv.apply_symm_apply, ULift.down_up] using
    terminalDerived_unitKummerClass X n hn hu
      ((sectionsEquiv.{u + 1} (Scheme.Etale.mk (𝟙 X))
        (multiplicativeSheaf.{u, 0} X)).symm (ULift.up s))

/-- A separately proved source equality identifies its ordinary Kummer boundary. -/
lemma terminalDerived_unitKummerClass_of_source_eq (n : ℕ) (hn : n ≠ 0)
    (hu : IsUnit (n : Γ(X, ⊤))) (s : Additive (Γ(X, ⊤))ˣ)
    (a : (DerivedCategory.singleFunctor _ 0).obj
        ((freeYoneda.{u + 1} X.smallEtaleTopology).obj (Scheme.Etale.mk (𝟙 X))) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (multiplicativeSheaf.{u, 0} X))
    (ha : a = (DerivedCategory.singleFunctor _ 0).map
      ((sectionsEquiv.{u + 1} (Scheme.Etale.mk (𝟙 X))
        (multiplicativeSheaf.{u, 0} X)).symm (ULift.up s))) :
    terminalDerivedHomAddEquivH.{w, w', u + 1} X.smallEtaleTopology
      (rootsOfUnitySheaf.{u, 0} X n) (Scheme.Etale.mk (𝟙 X))
      (MorphismProperty.Over.mkIdTerminal _ _) 1
      (a ≫ (kummerSequence_shortExact.{u, 0} X hn hu).extClass.hom) =
    unitKummerClass.{w, u, 0} X hn hu s := by
  rw [ha]
  exact terminalDerived_unitKummerClass_sections X n hn hu s

end Stacks.Kummer

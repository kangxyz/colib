/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.KummerUnitsModulo
public import Colib.CategoryTheory.Sites.TerminalCohomologyDegreeOne

/-! # The original terminal free-source boundary is the actual unit Kummer class -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.Cohomology.FreeYonedaUnivLE
universe w w' u
namespace Stacks.Kummer
variable (X : Scheme.{u})
variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The original derived terminal boundary of a free-source unit is its original Kummer class. -/
lemma terminalDerived_unitKummerClass (n : ℕ) (hn : n ≠ 0) (hu : IsUnit (n : Γ(X, ⊤)))
    (h : (freeYoneda.{u + 1} X.smallEtaleTopology).obj (Scheme.Etale.mk (𝟙 X)) ⟶
      multiplicativeSheaf.{u, 0} X) :
    terminalDerivedHomAddEquivH.{w, w', u + 1} X.smallEtaleTopology (rootsOfUnitySheaf.{u, 0} X n)
      (Scheme.Etale.mk (𝟙 X)) (MorphismProperty.Over.mkIdTerminal _ _) 1
      ((DerivedCategory.singleFunctor _ 0).map h ≫
        (kummerSequence_shortExact.{u, 0} X hn hu).extClass.hom) =
    unitKummerClass.{w, u, 0} X hn hu
      (sectionsEquiv.{u + 1} (Scheme.Etale.mk (𝟙 X)) (multiplicativeSheaf.{u, 0} X) h).down := by
  exact terminalDerivedHomAddEquivH_zero_comp.{w, w', u + 1}
    X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) (MorphismProperty.Over.mkIdTerminal _ _)
    h (kummerSequence_shortExact.{u, 0} X hn hu).extClass

end Stacks.Kummer

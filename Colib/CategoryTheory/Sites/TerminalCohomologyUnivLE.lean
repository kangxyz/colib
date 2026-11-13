/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import Colib.Util.References

/-!
# Terminal-object cohomology with an independent coefficient universe

The lifted free representable used by actual motivic hypercohomology agrees,
at a terminal object, with the constant integer sheaf defining ordinary
`Sheaf.H`. This extends the pinned-universe comparison in
`Stacks.Cohomology.TerminalCohomology`, reusing its free-group calculation.
Adapted from `StacksFrontier/CategoryTheory/Sites/GlobalSections/
CohomologyAtTheTerminalObject.lean` at the pinned Stacks revision.
No étale Tate identification or big/small-site equivalence is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w w' t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C]

/-- The universe-lifted representable of a terminal object is the singleton presheaf. -/
def uliftYonedaTerminalIsoConstPUnit (U : C) (hU : IsTerminal U) :
    (uliftYoneda.{t}).obj U ≅ (Functor.const Cᵒᵖ).obj (PUnit.{max v t + 1}) :=
  NatIso.ofComponents
    (fun V => Equiv.toIso
      (@Equiv.equivPUnit _ ⟨⟨ULift.up (hU.from V.unop)⟩,
        fun f => by apply ULift.ext; exact hU.hom_ext _ _⟩))
    (fun _ => rfl)

/-- The free abelian presheaf on the lifted terminal representable is constant integers. -/
def freeYonedaTerminalIsoConstULiftInt (U : C) (hU : IsTerminal U) :
    (uliftYoneda.{t}).obj U ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{max v t} ℤ)) :=
  Functor.isoWhiskerRight (uliftYonedaTerminalIsoConstPUnit U hU) AddCommGrpCat.free ≪≫
    Functor.constComp _ _ _ ≪≫ (Functor.const Cᵒᵖ).mapIso
      TerminalCohomology.freeObjPUnitIsoULiftInt

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max v t}]

/-- The actual lifted free terminal sheaf is the constant integer sheaf defining `Sheaf.H`. -/
def freeYonedaTerminalIsoConstantSheaf (U : C) (hU : IsTerminal U) :
    (freeYoneda.{t} J).obj U ≅
      (constantSheaf J AddCommGrpCat.{max v t}).obj
        (AddCommGrpCat.of (ULift.{max v t} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{max v t}).mapIso
    (freeYonedaTerminalIsoConstULiftInt U hU)

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Terminal cohomology with lifted coefficients is ordinary sheaf cohomology,
naturally in the coefficient sheaf. -/
@[colib_tag "COL-1226",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/CategoryTheory/Sites/GlobalSections/CohomologyAtTheTerminalObject.lean"
    "generalization" "Independent coefficient universes in terminal-source Ext and derived-Hom"]
def terminalCohomologyFunctorIso (U : C) (hU : IsTerminal U) (n : ℕ) :
    cohomologyPresheafFunctor.{w, t} J n ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U) ≅
      (Sheaf.functorH J n : Sheaf J AddCommGrpCat.{max v t} ⥤ AddCommGrpCat.{w}) :=
  (extFunctor n).mapIso (freeYonedaTerminalIsoConstantSheaf J U hU).symm.op

/-- The additive comparison from the actual terminal free-source Ext group to `Sheaf.H`. -/
def terminalCohomologyAddEquiv (F : Sheaf J AddCommGrpCat.{max v t})
    (U : C) (hU : IsTerminal U) (n : ℕ) :
    (cohomologyPresheaf.{w, t} F n).obj (op U) ≃+ Sheaf.H.{w} F n :=
  ((terminalCohomologyFunctorIso J U hU n).app F).addCommGroupIsoToAddEquiv

/-- The comparison intertwines the original coefficient maps on both cohomology functors. -/
theorem terminalCohomologyFunctorIso_naturality {F G : Sheaf J AddCommGrpCat.{max v t}}
    (f : F ⟶ G) (U : C) (hU : IsTerminal U) (n : ℕ) :
    ((cohomologyPresheafFunctor.{w, t} J n).map f).app (op U) ≫
        (terminalCohomologyFunctorIso J U hU n).hom.app G =
      (terminalCohomologyFunctorIso J U hU n).hom.app F ≫
        (Sheaf.functorH J n).map f :=
  (terminalCohomologyFunctorIso J U hU n).hom.naturality f

variable [HasDerivedCategory.{w'} (Sheaf J AddCommGrpCat.{max v t})]

/-- Genuine derived morphisms from the terminal representing sheaf to a shifted
single coefficient sheaf compute the existing ordinary `Sheaf.H`. -/
@[colib_tag "COL-1226",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/CategoryTheory/Sites/GlobalSections/CohomologyAtTheTerminalObject.lean"
    "generalization" "Independent coefficient universes in terminal-source Ext and derived-Hom"]
def terminalDerivedHomAddEquivH (F : Sheaf J AddCommGrpCat.{max v t})
    (U : C) (hU : IsTerminal U) (n : ℕ) :
    ((DerivedCategory.singleFunctor _ 0).obj ((freeYoneda.{t} J).obj U) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj F)⟦(n : ℤ)⟧) ≃+ Sheaf.H.{w} F n :=
  Ext.homAddEquiv.symm.trans (terminalCohomologyAddEquiv J F U hU n)

end Stacks.Cohomology.FreeYonedaUnivLE

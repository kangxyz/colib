/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Sites.TerminalCohomologyUnivLE

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe w u

noncomputable section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{u + 1})]
  (U : C) (hU : IsTerminal U) (n : ℕ)

-- The actual coefficient universe is strictly above the morphism universe.
example (F : Sheaf J AddCommGrpCat.{u + 1}) :
    (cohomologyPresheaf.{w, u + 1} F n).obj (op U) ≃+ Sheaf.H.{w} F n :=
  terminalCohomologyAddEquiv J F U hU n

example {F G : Sheaf J AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    ((cohomologyPresheafFunctor.{w, u + 1} J n).map f).app (op U) ≫
        (terminalCohomologyFunctorIso J U hU n).hom.app G =
      (terminalCohomologyFunctorIso J U hU n).hom.app F ≫
        (Sheaf.functorH J n).map f :=
  terminalCohomologyFunctorIso_naturality J f U hU n

example [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{u + 1})]
    (F : Sheaf J AddCommGrpCat.{u + 1}) :
    ((DerivedCategory.singleFunctor _ 0).obj ((freeYoneda.{u + 1} J).obj U) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj F)⟦(n : ℤ)⟧) ≃+ Sheaf.H.{w} F n :=
  terminalDerivedHomAddEquivH J F U hU n

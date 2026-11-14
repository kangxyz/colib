/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.CategoryTheory.Sites.TerminalCohomologyDegreeZero
import Colib.AlgebraicGeometry.Sites.Smooth.Etale.SourceSections
import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.SourceSections

/-! # Native source-section compatibility regressions -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme Stacks.Cohomology.FreeYonedaUnivLE
universe w t v u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

example {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max v t}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]
    (F : Sheaf J AddCommGrpCat.{max v t}) (U : C) (hU : IsTerminal U)
    (f : (freeYoneda.{t} J).obj U ⟶ F) :
    Sheaf.H.equiv₀ F hU (terminalCohomologyAddEquiv J F U hU 0 (Ext.mk₀ f)) =
      sectionsEquiv U F f := terminalCohomologyAddEquiv_zero J F U hU f

example (S : Scheme.{u})
    [HasSheafify (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}]
    (X : SmoothSite S)
    (f : (freeYoneda.{u + 1} (SmoothSite.nisnevichTopology S)).obj X ⟶
      SmoothSite.largeUnitsSheaf S) :
    sectionsEquiv.{u + 1} X (SmoothSite.largeUnitsEtaleSheaf S)
      ((SmoothSite.nisnevichToEtaleFreeYonedaIso S).inv.app X ≫
        (SmoothSite.nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).map f ≫
        (SmoothSite.nisnevichToEtaleLargeUnitsIso S).hom) =
      sectionsEquiv.{u + 1} X (SmoothSite.largeUnitsSheaf S) f :=
  SmoothSite.nisnevichToEtaleFreeYonedaIso_units S X f

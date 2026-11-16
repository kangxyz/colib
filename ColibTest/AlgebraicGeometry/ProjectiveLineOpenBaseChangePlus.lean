/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.OpenBaseChangePlus

/-! # Public API for canonical open base change on bounded-below objects -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.projectiveSpaceOver

universe u

attribute [local instance] HasDerivedCategory.standard

example {S T : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g]
    (K : DerivedCategory.Plus (projectiveSpaceOver 1 S).Modules) :
    IsIso ((projectiveLineOpenBaseChangePlus g).app K) :=
  isIso_projectiveLineOpenBaseChangePlus_app g K

example {S T : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g]
    {K L : DerivedCategory.Plus (projectiveSpaceOver 1 S).Modules} (r : K ⟶ L) :
    let τ := projectiveLineOpenBaseChangePlus g
    ∃ e, e = τ.naturality r :=
  ⟨_, rfl⟩

example {S T : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g]
    (K : DerivedCategory.Plus (projectiveSpaceOver 1 S).Modules) :
    (projectiveLineOpenBaseChangePlusIso g).hom.app K =
      (projectiveLineOpenBaseChangePlus g).app K := by
  exact projectiveLineOpenBaseChangePlusIso_hom_app g K

#print axioms isIso_projectiveLineOpenBaseChangePlus_app
#print axioms projectiveLineOpenBaseChangePlusIso_hom_app
#print axioms projectiveLineOpenBaseChangePlusIso_unit

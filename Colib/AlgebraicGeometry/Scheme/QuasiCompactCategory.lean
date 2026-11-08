/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The full category of quasi-compact schemes -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- Quasi-compact schemes, without any separatedness or finiteness condition on morphisms. -/
def quasiCompactScheme : ObjectProperty Scheme.{u} := fun X => CompactSpace X

/-- The actual full subcategory of native schemes with quasi-compact underlying space. -/
abbrev QuasiCompactSchemes := (quasiCompactScheme.{u}).FullSubcategory

instance (X : QuasiCompactSchemes.{u}) : CompactSpace X.obj := X.property

/-- The literal inclusion, retaining every native scheme morphism. -/
def quasiCompactSchemesInclusion : QuasiCompactSchemes.{u} ⥤ Scheme.{u} :=
  quasiCompactScheme.ι

end AlgebraicGeometry.Scheme

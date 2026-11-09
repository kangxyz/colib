/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Coproducts.Zero

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable (k : Type u) [Field k]

example {X Y : Cor k} [IsEmpty X.toSmoothSite.left] (α : X ⟶ Y) : α = 0 :=
  Cor.hom_eq_zero_of_isEmpty_source k α

example {X Y : Cor k} [IsEmpty Y.toSmoothSite.left] (α : X ⟶ Y) : α = 0 :=
  Cor.hom_eq_zero_of_isEmpty_target k α

example : IsZero (Cor.empty k) := Cor.empty_isZero k

example : HasZeroObject (Cor k) := inferInstance

example (X : Cor k) : Subsingleton (Cor.empty k ⟶ X) := inferInstance

example (X : Cor k) : Subsingleton (X ⟶ Cor.empty k) := inferInstance

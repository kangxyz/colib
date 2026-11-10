/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Intersection.SmoothDiagonalGraphList

/-! # Direct consumers on the literal source-first graph product -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

variable {S Y X : Scheme.{u}} (g : Y ⟶ S) (f : X ⟶ Y)

example :
    (Scheme.Hom.diagonalBaseChangeGraphIso g f).inv ≫
      pullback.fst (pullback.fst g g) f =
        pullback.map (f ≫ g) g g g f (𝟙 Y) (𝟙 S) (by simp) (by simp) :=
  Scheme.Hom.diagonalBaseChangeGraphIso_inv_fst g f

example [Smooth g] [IsLocallyNoetherian X]
    (z : pullback (C := Scheme) (f ≫ g) g) (y : Y)
    (hz : (pullback.map (f ≫ g) g g g f (𝟙 Y) (𝟙 S) (by simp) (by simp)) z =
      pullback.diagonal g y) :
    let γ := pullback.map (f ≫ g) g g g f (𝟙 Y) (𝟙 S) (by simp) (by simp)
    ∃ (r : ℕ) (b : Fin r → (pullback g g).presheaf.stalk (γ z)),
      IsRegular ((pullback g g).presheaf.stalk (γ z)) (List.ofFn b) ∧
      Ideal.span (Set.range b) = RingHom.ker
        (((pullback g g).presheaf.stalkCongr (.of_eq hz)).hom ≫
          (pullback.diagonal g).stalkMap y).hom ∧
      IsRegular ((pullback (f ≫ g) g).presheaf.stalk z)
        (List.ofFn (fun i => (γ.stalkMap z).hom (b i))) :=
  Scheme.Hom.exists_isRegular_diagonalStalkList_graphPair g f z y hz

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteScalarTriangle

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- This is the actual action, for any point of the whole nonreduced finite model.
example (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (a : correspondenceRemainingImageStalk f g h i z w v x) :
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    let R := correspondenceRemainingImageStalk f g h i z w v x
    let B := correspondenceRemainingFiniteRing f g h i z w v x
    let E := correspondenceRemainingFiniteModel f g h i z w v x
    let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
    (E).presheaf.germ ⊤ q trivial (algebraMap R B a) =
      π.stalkMap q ((Spec R).presheaf.germ ⊤ (π q) trivial ((Scheme.ΓSpecIso R).inv a)) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  exact congrArg (fun φ => φ a) (correspondenceRemainingFiniteAlgebra_germ f g h i z w v x q)

-- The equality retains the entire ordered original middle list, not just its generated ideal.
example (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) {r : ℕ}
    (s : Fin r → (pullback (C := Scheme) h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x))) :
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    let R := correspondenceRemainingImageStalk f g h i z w v x
    let B := correspondenceRemainingFiniteRing f g h i z w v x
    let E := correspondenceRemainingFiniteModel f g h i z w v x
    let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
    (fun j => (E).presheaf.germ ⊤ q trivial (algebraMap R B (α (s j)))) =
      (fun j => π.stalkMap q
        ((Spec R).presheaf.germ ⊤ (π q) trivial ((Scheme.ΓSpecIso R).inv (α (s j))))) :=
  correspondenceRemainingFiniteAlgebra_germ_middleList f g h i z w v x q s

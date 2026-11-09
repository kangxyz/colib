/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteScalarTriangle

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let π := correspondenceRightRemainingFiniteModelStructure f g h i z w v x
    ((E).presheaf.germ ⊤ q trivial).hom.comp (algebraMap R B) =
      (π.stalkMap q).hom.comp
        (((Spec R).presheaf.germ ⊤ (π q) trivial).hom.comp (Scheme.ΓSpecIso R).inv.hom) := by
  exact correspondenceRightRemainingFiniteAlgebra_germ
    f g h i z w v x q

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) {r : ℕ}
    (s : Fin r → (pullback (C := Scheme) g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x))) :
    let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let π := correspondenceRightRemainingFiniteModelStructure f g h i z w v x
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    (fun j => (E).presheaf.germ ⊤ q trivial (algebraMap R B (α (s j)))) =
      (fun j => π.stalkMap q
        ((Spec R).presheaf.germ ⊤ (π q) trivial ((Scheme.ΓSpecIso R).inv (α (s j))))) := by
  exact correspondenceRightRemainingFiniteAlgebra_germ_middleList
    f g h i z w v x q s

end Stacks.Chow

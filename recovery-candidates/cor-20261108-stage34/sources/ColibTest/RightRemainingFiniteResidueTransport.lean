/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import
  Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteResidueTransport

/-! Literal endpoint consumers. Source-only; no compilation or kernel check performed. -/

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
    (Ideal.comap
      ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial).hom
      (IsLocalRing.maximalIdeal
        ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q))).comap
      (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
        (correspondenceRightRemainingFiniteRing f g h i z w v x)) =
      (correspondenceRightRemainingFiniteModelStructure f g h i z w v x q).asIdeal := by
  exact correspondenceRightRemainingFiniteGermPrime_comap_algebraMap
    f g h i z w v x q

example [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree
      (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
        (correspondenceRightRemainingFiniteRing f g h i z w v x))
      ((Ideal.comap
        ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal
          ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q))).comap
        (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
          (correspondenceRightRemainingFiniteRing f g h i z w v x)))
      (Ideal.comap
        ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal
          ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q))) =
      (correspondenceRightIntermediateImageMap f g h i z w v).residueDegree
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) := by
  exact primeResidueDegree_correspondenceRightRemainingFiniteAlgebra
    f g h i z w v hw hv x q

end Stacks.Chow

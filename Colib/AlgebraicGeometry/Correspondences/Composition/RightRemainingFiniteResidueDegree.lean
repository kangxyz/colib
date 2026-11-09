/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteModel
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartFibre

/-!
# Original right residue degrees from the actual finite model

The native affine/germ residue-degree theorem is applied to the actual full
finite model over the spectrum of the actual image stalk. Both coordinate-ring
primes are the actual germ preimages of stalk maximal ideals. The resulting
degree is the degree of the original full exterior finite morphism, by the
already proved stalk-localization comparison.

This does not reprove the affine residue-field theorem from its lower inputs.
Its owner is `Spaces.ElementaryChartFibre`, although the theorem used here is
about schemes. The action normalization also records the exact `ΓSpecIso`
through which the original image-stalk ring acts on the full finite algebra.
Transport of prime residue degrees along that ring isomorphism remains separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual coordinate-ring residue degree is the original full exterior
finite-map degree. No reducedness, geometric integrality or perfect field is used. -/
theorem primeResidueDegree_correspondenceRightRemainingFiniteModel [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    Stacks.Length.primeResidueDegree
      (correspondenceRightRemainingFiniteModelStructure f g h i z w v x).appTop.hom
      (Ideal.comap
        ((Spec (correspondenceRightRemainingImageStalk f g h i z w v x)).presheaf.germ ⊤
          (correspondenceRightRemainingFiniteModelStructure f g h i z w v x q) trivial).hom
        (IsLocalRing.maximalIdeal
          ((Spec (correspondenceRightRemainingImageStalk f g h i z w v x)).presheaf.stalk
            (correspondenceRightRemainingFiniteModelStructure f g h i z w v x q))))
      (Ideal.comap
        ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal
          ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q))) =
      (correspondenceRightIntermediateImageMap f g h i z w v).residueDegree
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) := by
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  exact (Scheme.primeResidueDegree_comap_germ_eq_residueDegree
    (correspondenceRightRemainingFiniteModelStructure f g h i z w v x) q).trans
      (residueDegree_correspondenceRightRemainingFiniteModelStructure f g h i z w v x q)

end Stacks.Chow

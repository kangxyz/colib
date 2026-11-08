/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteModel
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartFibre

/-!
# Original residue degrees from the actual finite model

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

/-- The scalar map is the native actual structure map after `ΓSpecIso`, not an
arbitrary algebra structure on the same carrier. -/
theorem correspondenceRemainingFiniteAlgebra_algebraMap
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
      (correspondenceRemainingFiniteRing f g h i z w v x) =
      ((Scheme.ΓSpecIso (correspondenceRemainingImageStalk f g h i z w v x)).inv ≫
        (correspondenceRemainingFiniteModelStructure f g h i z w v x).appTop).hom := by
  let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
  change ((Scheme.ΓSpecIso (correspondenceRemainingImageStalk f g h i z w v x)).inv ≫
    π.appLE ⊤ ⊤
      (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top π ⊤)).hom = _
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop, π]

/-- The actual coordinate-ring residue degree is the original full exterior
finite-map degree. No reducedness, geometric integrality or perfect field is used. -/
theorem primeResidueDegree_correspondenceRemainingFiniteModel [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) :
    Stacks.Length.primeResidueDegree
      (correspondenceRemainingFiniteModelStructure f g h i z w v x).appTop.hom
      (Ideal.comap
        ((Spec (correspondenceRemainingImageStalk f g h i z w v x)).presheaf.germ ⊤
          (correspondenceRemainingFiniteModelStructure f g h i z w v x q) trivial).hom
        (IsLocalRing.maximalIdeal
          ((Spec (correspondenceRemainingImageStalk f g h i z w v x)).presheaf.stalk
            (correspondenceRemainingFiniteModelStructure f g h i z w v x q))))
      (Ideal.comap
        ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal
          ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q))) =
      (correspondenceLeftIntermediateImageMap f g h i z w v).residueDegree
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q) := by
  let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  exact (Scheme.primeResidueDegree_comap_germ_eq_residueDegree
    (correspondenceRemainingFiniteModelStructure f g h i z w v x) q).trans
      (residueDegree_correspondenceRemainingFiniteModelStructure f g h i z w v x q)

end Stacks.Chow

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageExteriorSquare
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteModel

/-!
# Finite full exterior fibre multiplicities at the actual generic model labels

The actual image-Euler hypotheses imply that the full source exterior is locally
Noetherian because its actual map to the image exterior is finite. Every generic
model label projects to a generic source point. Its local ring is therefore
Artinian, so the actual closed-fibre quotient has finite length. This certificate
uses no Tor sheaf, module-family truncation, or assumption that a coefficient is
nonzero. It supplies the finiteness needed before interpreting ENat.toNat as a
cycle multiplicity in the concrete correspondence scope.
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

/-- The full exterior fibre factor is genuinely finite at every generic model label under
exactly the actual image-Euler hypotheses, not only an extended-length truncation. -/
theorem length_correspondenceRemainingExteriorFiber_ne_top [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : genericPoints
      (correspondenceRemainingFiniteModel f g h i z w v x)) :
    let y := correspondenceRemainingFiniteModelProjection f g h i z w v x q.1
    Module.length
      ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk y)
      ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk y ⧸
        Ideal.map ((correspondenceLeftExteriorProjection f g h i z w v).stalkMap y).hom
          (IsLocalRing.maximalIdeal ((correspondenceIncidence f g h z w).presheaf.stalk
            (correspondenceLeftExteriorProjection f g h i z w v y)))) ≠ ⊤ := by
  let := isLocallyNoetherian_correspondenceLeftIntermediateSupportProduct_of_image
    f g h i z w v hz hw
  exact length_correspondenceLeftExteriorFiber_ne_top f g h i z w v
    (correspondenceRemainingFiniteGenericLabel f g h i z w v x q)

end Stacks.Chow

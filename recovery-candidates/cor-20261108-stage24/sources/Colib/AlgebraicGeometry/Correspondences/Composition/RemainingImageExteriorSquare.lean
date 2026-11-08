/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImage
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorMultiplicity

/-!
# The full intermediate-image exterior square

The actual whole first-incidence exterior and the whole intermediate-image
exterior form a Cartesian square over the original incidence-to-image map.
These are geometric objects before any choice of coefficient sheaf, Tor degree,
or local finite algebra. No reduction, integral-component replacement, or
flatness of the finite image map is used. The actual finite map also transports
local Noetherianness from the image exterior to the source exterior.
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

/-- The projection from the whole image exterior to the whole original intermediate image. -/
abbrev correspondenceLeftImageExteriorProjection :
    correspondenceLeftIntermediateImageProduct f g h i z w v ⟶
      correspondenceIntermediateImage f g h z w :=
  pullback.fst _ _

/-- The actual finite exterior map commutes with the two original projections. -/
@[reassoc]
theorem correspondenceLeftIntermediateImageMap_projection :
    correspondenceLeftIntermediateImageMap f g h i z w v ≫
        correspondenceLeftImageExteriorProjection f g h i z w v =
      correspondenceLeftExteriorProjection f g h i z w v ≫
        (correspondenceIncidenceMap f g h z w).toImage := by
  simp [correspondenceLeftIntermediateImageMap, correspondenceLeftImageExteriorProjection,
    correspondenceLeftExteriorProjection]

/-- The full image square is Cartesian, before any reduction or restriction to generic points. -/
theorem correspondenceLeftIntermediateImageMap_isPullback :
    IsPullback (correspondenceLeftExteriorProjection f g h i z w v)
      (correspondenceLeftIntermediateImageMap f g h i z w v)
      (correspondenceIncidenceMap f g h z w).toImage
      (correspondenceLeftImageExteriorProjection f g h i z w v) := by
  have hp : IsPullback
      (correspondenceLeftExteriorProjection f g h i z w v)
      (correspondenceLeftIntermediateImageMap f g h i z w v ≫ pullback.snd _ _)
      ((correspondenceIncidenceMap f g h z w).toImage ≫
        (correspondenceIntermediateImageTarget f g h z w ≫ h))
      (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) := by
    simpa only [correspondenceLeftExteriorProjection, correspondenceLeftIntermediateImageMap,
      pullback.map, pullback.lift_snd, Category.comp_id, correspondenceIntermediateImageTarget,
      ← Category.assoc, Scheme.Hom.toImage_imageι, correspondenceIncidenceMap_snd] using
      (IsPullback.of_hasPullback (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h))
  exact hp.of_bot (correspondenceLeftIntermediateImageMap_projection f g h i z w v).symm
    (IsPullback.of_hasPullback (correspondenceIntermediateImageTarget f g h z w ≫ h)
      (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h))

/-- The full source exterior is locally Noetherian under the actual Euler hypotheses.
This follows from its finite map to the full image exterior, without another support hypothesis. -/
theorem isLocallyNoetherian_correspondenceLeftIntermediateSupportProduct_of_image
    [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    IsLocallyNoetherian (correspondenceLeftIntermediateSupportProduct f g h i z w v) := by
  let := isFinite_correspondenceLeftIntermediateImageMap f g h i z w v hz hw
  exact LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceLeftIntermediateImageMap f g h i z w v)

end Stacks.Chow

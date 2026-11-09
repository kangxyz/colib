/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImage

/-!
# The actual right finite-image exterior square

The original G,H incidence maps to its full image. Its base change is the actual
right map, with the original first support on the left. Both projections in this
square are the second pullback projections. The proof uses the actual Cartesian
products in this order, not a transposed admissible correspondence. No flatness,
reducedness or generic-point hypothesis is required. This is the square for native
02RG in the right weighted replacement. See motivic a6805c4,
Composition/Incidence/RightComposition.lean, blob 856b38b20a15444e6491366eb2406f21124bfdc5.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- Project the full right image exterior to the original full G,H image. -/
abbrev correspondenceRightImageExteriorProjection :
    correspondenceRightIntermediateImageProduct f g h i z w v ⟶
      correspondenceIntermediateImage g h i w v :=
  pullback.snd _ _

/-- The finite exterior map preserves the actual original second-factor projections. -/
@[reassoc]
theorem correspondenceRightIntermediateImageMap_projection :
    correspondenceRightIntermediateImageMap f g h i z w v ≫
        correspondenceRightImageExteriorProjection f g h i z w v =
      correspondenceRightExteriorProjection f g h i z w v ≫
        (correspondenceIncidenceMap g h i w v).toImage := by
  simp [correspondenceRightIntermediateImageMap, correspondenceRightImageExteriorProjection,
    correspondenceRightExteriorProjection]

/-- The whole right finite-image square is Cartesian before taking any component or Tor. -/
theorem correspondenceRightIntermediateImageMap_isPullback :
    IsPullback (correspondenceRightExteriorProjection f g h i z w v)
      (correspondenceRightIntermediateImageMap f g h i z w v)
      (correspondenceIncidenceMap g h i w v).toImage
      (correspondenceRightImageExteriorProjection f g h i z w v) := by
  let a := ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g
  let b := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
  have hp : IsPullback
      (correspondenceRightExteriorProjection f g h i z w v)
      (correspondenceRightIntermediateImageMap f g h i z w v ≫ pullback.fst _ _)
      ((correspondenceIncidenceMap g h i w v).toImage ≫ b) a := by
    simpa only [correspondenceRightExteriorProjection, correspondenceRightIntermediateImageMap,
      pullback.map, pullback.lift_fst, Category.comp_id, b, ← Category.assoc,
      Scheme.Hom.toImage_imageι, correspondenceIncidenceMap_fst] using
      (IsPullback.of_hasPullback a (correspondenceIncidenceLeft g h i w v ≫ g)).flip
  exact hp.of_bot (correspondenceRightIntermediateImageMap_projection f g h i z w v).symm
    (IsPullback.of_hasPullback a b).flip

end Stacks.Chow

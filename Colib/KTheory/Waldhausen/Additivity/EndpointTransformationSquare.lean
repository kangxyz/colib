/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.EndpointTransformationSquare
public import Colib.KTheory.Waldhausen.Additivity.MixedTransformationSquare
public import Colib.KTheory.Waldhausen.Additivity.NormalizedEndpointHomotopies
public import Colib.KTheory.Waldhausen.WeakGridSquareRealization

/-! Implementation provenance: `Quillen/Waldhausen/Additivity/EndpointTransformationSquare.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, hypotheses, universes,
whole faces and chosen-zero surfaces are preserved. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SSet SSet.MixedOrdinalCylinder
open scoped Simplicial Topology unitInterval
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G H F' G' H' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')
  (ηF : F ⟶ F') (ηG : G ⟶ G') (haη : a ≫ ηG = ηF ≫ a')
  (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X))

/-- The realized unreversed identity square keeps transformation time first. -/
def normalizedIdentityEndpointTransformationRealizationSquare :
    C(unitInterval × (unitInterval × |SSet.diagonalSSet (bisimplicialSSet V)|),
      |SSet.diagonalSSet (bisimplicialSSet W)|) :=
  realizationDoubleCylinderSquare
    (normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG)

/-- The whole realized transformation zero face has its unchanged parametrization. -/
theorem normalizedIdentityEndpointTransformationRealizationSquare_transformation_zero
    (s : unitInterval) (x : |SSet.diagonalSSet (bisimplicialSSet V)|) :
    normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG (0, (s, x)) =
      normalizedIdentityEndpointRealizationHomotopy V W a hs.exactF hs.exactG hs.cofibration (s, x)
        :=
  realizationDoubleCylinderSquare_vertical_zero
    (normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (normalizedIdentityEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointTransformationSquare_transformation_zero V W a a' b b' hs hs' ηF ηG
      haη hηF hηG) s x

/-- The whole realized transformation one face has its unchanged parametrization. -/
theorem normalizedIdentityEndpointTransformationRealizationSquare_transformation_one
    (s : unitInterval) (x : |SSet.diagonalSSet (bisimplicialSSet V)|) :
    normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG (1, (s, x)) =
      normalizedIdentityEndpointRealizationHomotopy V W a' hs'.exactF hs'.exactG hs'.cofibration
        (s, x) :=
  realizationDoubleCylinderSquare_vertical_one
    (normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (normalizedIdentityEndpointHomotopy V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedIdentityEndpointTransformationSquare_transformation_one V W a a' b b' hs hs' ηF ηG
      haη hηF hηG) s x

/-- The whole realized endpoint zero face has its unchanged parametrization. -/
theorem normalizedIdentityEndpointTransformationRealizationSquare_endpoint_zero
    (t : unitInterval) (x : |SSet.diagonalSSet (bisimplicialSSet V)|) :
    normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG (t, (0, x)) =
      realizationSimplicialHomotopy (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs'
        ηF ηG haη hηF hηG) (t, x) :=
  realizationDoubleCylinderSquare_horizontal_zero
    (normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (normalizedIdentityEndpointTransformationSquare_endpoint_zero V W a a' b b' hs hs' ηF ηG haη
      hηF hηG) t x

/-- The whole realized endpoint one face has its unchanged parametrization. -/
theorem normalizedIdentityEndpointTransformationRealizationSquare_endpoint_one
    (t : unitInterval) (x : |SSet.diagonalSSet (bisimplicialSSet V)|) :
    normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG (t, (1, x)) =
      realizationSimplicialHomotopy (normalizedMiddleTransformationHomotopy V W a a' b b' hs hs' ηG
        hηG) (t, x) :=
  realizationDoubleCylinderSquare_horizontal_one
    (normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (normalizedMiddleTransformationHomotopy V W a a' b b' hs hs' ηG hηG)
    (normalizedIdentityEndpointTransformationSquare_endpoint_one V W a a' b b' hs hs' ηF ηG haη hηF
      hηG) t x

/-- Both continuous times fix the actual chosen zero throughout the identity square. -/
theorem normalizedIdentityEndpointTransformationRealizationSquare_fixed_zero
    (t s : unitInterval) :
    normalizedIdentityEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
      (t, (s, realizationPoint (diagonalZeroVertex V))) =
        realizationPoint (diagonalZeroVertex W) :=
  realizationDoubleCylinderSquare_fixed_vertex
    (normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ _
    (normalizedIdentityEndpointTransformationSquare_fixed_zero V W a a' b b' hs hs' ηF ηG haη hηF
      hηG) t s

variable [HasBinaryCoproducts D]
  (ηH : H ⟶ H') (hbη : b ≫ ηH = ηG ≫ b') (hηH : ∀ X, W.weq (ηH.app X))

/-- The realized unreversed separated square keeps transformation time first. -/
def normalizedSeparatedEndpointTransformationRealizationSquare :
    C(unitInterval × (unitInterval × |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙
      bisimplicialSSet V)|), |SSet.diagonalSSet (bisimplicialSSet W)|) :=
  realizationDoubleCylinderSquare
    (normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG ηH hbη
      hηH)

/-- The whole realized transformation zero face has its unchanged parametrization. -/
theorem normalizedSeparatedEndpointTransformationRealizationSquare_transformation_zero
    (s : unitInterval) (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|)
      :
    normalizedSeparatedEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH (0, (s, x)) =
      normalizedSeparatedEndpointRealizationHomotopy V W a b hs (s, x) :=
  realizationDoubleCylinderSquare_vertical_zero
    (normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG ηH hbη
      hηH)
    (normalizedSeparatedEndpointHomotopy V W a b hs)
    (normalizedSeparatedEndpointTransformationSquare_transformation_zero V W a a' b b' hs hs' ηF ηG
      haη hηF hηG ηH hbη hηH) s x

/-- The whole realized transformation one face has its unchanged parametrization. -/
theorem normalizedSeparatedEndpointTransformationRealizationSquare_transformation_one
    (s : unitInterval) (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|)
      :
    normalizedSeparatedEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH (1, (s, x)) =
      normalizedSeparatedEndpointRealizationHomotopy V W a' b' hs' (s, x) :=
  realizationDoubleCylinderSquare_vertical_one
    (normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG ηH hbη
      hηH)
    (normalizedSeparatedEndpointHomotopy V W a' b' hs')
    (normalizedSeparatedEndpointTransformationSquare_transformation_one V W a a' b b' hs hs' ηF ηG
      haη hηF hηG ηH hbη hηH) s x

/-- The whole realized endpoint zero face has its unchanged parametrization. -/
theorem normalizedSeparatedEndpointTransformationRealizationSquare_endpoint_zero
    (t : unitInterval) (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|)
      :
    normalizedSeparatedEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH (t, (0, x)) =
      realizationSimplicialHomotopy (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs'
        ηF ηG haη hηF hηG) (t, x) :=
  realizationDoubleCylinderSquare_horizontal_zero
    (normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG ηH hbη
      hηH)
    (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (normalizedSeparatedEndpointTransformationSquare_endpoint_zero V W a a' b b' hs hs' ηF ηG haη
      hηF hηG ηH hbη hηH) t x

/-- The whole realized endpoint one face has its unchanged parametrization. -/
theorem normalizedSeparatedEndpointTransformationRealizationSquare_endpoint_one
    (t : unitInterval) (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|)
      :
    normalizedSeparatedEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH (t, (1, x)) =
      realizationSimplicialHomotopy (normalizedSumTransformationHomotopy V W a a' b b' hs hs' ηF
        hηF ηH hηH) (t, x) :=
  realizationDoubleCylinderSquare_horizontal_one
    (normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG ηH hbη
      hηH)
    (normalizedSumTransformationHomotopy V W a a' b b' hs hs' ηF hηF ηH hηH)
    (normalizedSeparatedEndpointTransformationSquare_endpoint_one V W a a' b b' hs hs' ηF ηG haη
      hηF hηG ηH hbη hηH) t x

/-- Both continuous times fix the actual subdivision zero throughout the separated square. -/
theorem normalizedSeparatedEndpointTransformationRealizationSquare_fixed_zero
    (t s : unitInterval) :
    normalizedSeparatedEndpointTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH
      (t, (s, subdivisionBasepoint V)) = realizationPoint (diagonalZeroVertex W) :=
  realizationDoubleCylinderSquare_fixed_vertex
    (normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG ηH hbη
      hηH) _ _
    (normalizedSeparatedEndpointTransformationSquare_fixed_zero V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH) t s


end CategoryTheory.Waldhausen.Additivity

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Additivity.BasedTransformationSquare

/-! Whole-map regression obligations: both transformation faces, both additivity faces,
the entire fixed-zero surface and the literal three-piece relative pasting. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory SSet
open scoped Simplicial Topology unitInterval
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
  {F G H F' G' H' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')
  (ηF : F ⟶ F') (ηG : G ⟶ G') (ηH : H ⟶ H')
  (haη : a ≫ ηG = ηF ≫ a') (hbη : b ≫ ηH = ηG ≫ b')
  (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X))
  (hηH : ∀ X, W.weq (ηH.app X))

example :
    (fun p : unitInterval × |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      ↦
      subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG
      hηH (0, (p.1, p.2))) =
    (fun p ↦ subdividedBasedAdditivityHomotopy V W a b hs p) := by
  funext p
  exact subdividedBasedAdditivityTransformationSquare_transformation_zero
    V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH p.1 p.2

example :
    (fun p : unitInterval × |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      ↦
      subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG
      hηH (1, (p.1, p.2))) =
    (fun p ↦ subdividedBasedAdditivityHomotopy V W a' b' hs' p) := by
  funext p
  exact subdividedBasedAdditivityTransformationSquare_transformation_one
    V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH p.1 p.2

example :
    (fun p : unitInterval × |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      ↦
      subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG
      hηH (p.1, (0, p.2))) =
    (fun p ↦ subdividedMiddleTransformationMap V W a a' b b' hs hs' ηG hηG p) := by
  funext p
  exact subdividedBasedAdditivityTransformationSquare_additivity_zero
    V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH p.1 p.2

example :
    (fun p : unitInterval × |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      ↦
      subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG
      hηH (p.1, (1, p.2))) =
    (fun p ↦ subdividedSumTransformationMap V W a a' b b' hs hs' ηF ηH hηF hηH p) := by
  funext p
  exact subdividedBasedAdditivityTransformationSquare_additivity_one
    V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH p.1 p.2

example :
    (fun p : unitInterval × unitInterval ↦
      subdividedBasedAdditivityTransformationSquare V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG
      hηH (p.1, (p.2, subdivisionBasepoint V))) =
    (fun _ ↦ realizationPoint (diagonalZeroVertex W)) := by
  funext p
  exact subdividedBasedAdditivityTransformationSquare_fixed_zero
    V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF hηG hηH p.1 p.2

-- The unchanged trans association fixes the original half/quarter/quarter clock.
example : subdividedBasedAdditivityTransformationHomotopy V W a a' b b' hs hs' ηF ηG ηH haη hbη hηF
      hηG hηH =
    (subdividedIdentityEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη
      hηF hηG).symm.trans
      ((subdividedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).trans
        (subdividedSeparatedEndpointTransformationHomotopy V W a a' b b' hs hs' ηF ηG ηH haη hbη
      hηF hηG hηH)) := rfl

end CategoryTheory.Waldhausen.Additivity

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedEndpointHomotopies
public import Colib.KTheory.Waldhausen.Additivity.SubdivisionBasepoint
public import Colib.KTheory.Waldhausen.CanonicalMap

/-! Implementation provenance: `Quillen/Waldhausen/Additivity/NormalizedEndpointHomotopies.lean` at
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
variable (V : Structure C) (W : Structure D) {F G H : C ⥤ D} (a : F ⟶ G)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (hc : IsCofibrationTransformation W a V)

/-- The actual realized identity-endpoint homotopy retains these exact maps. -/
def normalizedIdentityEndpointRealizationHomotopy :
    (SSet.toTop.map (SSet.diagonalMap (normalizedIdentityMap V W a hF hG hc))).hom.Homotopy
      (SSet.toTop.map (SSet.diagonalMap (bisimplicialSSetMap V.cof V.weq hG.rebase))).hom :=
  SSet.realizationSimplicialHomotopy (normalizedIdentityEndpointHomotopy V W a hF hG hc)

/-- The identity-endpoint homotopy is fixed at the actual chosen zero vertex. -/
theorem normalizedIdentityEndpointRealizationHomotopy_fixed_zero (t : unitInterval) :
    normalizedIdentityEndpointRealizationHomotopy V W a hF hG hc
      (t, SSet.realizationPoint (diagonalZeroVertex V)) = SSet.realizationPoint
        (diagonalZeroVertex W) :=
  SSet.realizationSimplicialHomotopy_fixed_vertex
    (normalizedIdentityEndpointHomotopy V W a hF hG hc) _ _
    (normalizedIdentityEndpointHomotopy_fixed_zero V W a hF hG hc) t

variable [HasBinaryCoproducts D]
variable (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

/-- The actual realized separated-endpoint homotopy retains these exact maps. -/
def normalizedSeparatedEndpointRealizationHomotopy :
    (SSet.toTop.map (SSet.diagonalMap
      (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration))).hom.Homotopy
      (SSet.toTop.map (SSet.diagonalMap (normalizedSumMap V W hs.exactH hs.exactF))).hom :=
  SSet.realizationSimplicialHomotopy (normalizedSeparatedEndpointHomotopy V W a b hs)

/-- The realized separated-endpoint homotopy is fixed at the actual
subdivision basepoint. -/
theorem normalizedSeparatedEndpointRealizationHomotopy_fixed_zero (t : unitInterval) :
    normalizedSeparatedEndpointRealizationHomotopy V W a b hs
      (t, subdivisionBasepoint V) = SSet.realizationPoint (diagonalZeroVertex W) :=
  SSet.realizationSimplicialHomotopy_fixed_vertex
    (normalizedSeparatedEndpointHomotopy V W a b hs) _ _
    (normalizedSeparatedEndpointHomotopy_fixed_zero V W a b hs) t


end CategoryTheory.Waldhausen.Additivity

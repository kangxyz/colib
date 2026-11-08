/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedMixedHomotopy
public import Colib.KTheory.Waldhausen.Additivity.SubdivisionBasepoint
public import Colib.KTheory.Waldhausen.CanonicalMap

/-! Implementation provenance: `Quillen/Waldhausen/Additivity/NormalizedMixedHomotopy.lean` at
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
variable (V : Structure C) (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (hc : IsCofibrationTransformation W a V)

/-- The realized deformation genuinely stays at the chosen target zero. -/
theorem normalizedMixedRealizationHomotopy_fixed_zero (t : unitInterval) :
    SSet.realizationSimplicialHomotopy (normalizedMixedEndpointHomotopy V W a hF hG hc)
      (t, SSet.realizationPoint
        (show (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)) _⦋0⦌ from
          zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (SSet.OrdinalSubdivision.δ.obj
            ⦋0⦌)) (op ⦋0⦌))) =
        SSet.realizationPoint (diagonalZeroVertex W) :=
  SSet.realizationSimplicialHomotopy_fixed_vertex _ _ _
    (normalizedMixedEndpointHomotopy_fixed_zero V W a hF hG hc) t


end CategoryTheory.Waldhausen.Additivity

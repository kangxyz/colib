/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.MixedTransformationSquare
public import Colib.KTheory.Waldhausen.Additivity.NormalizedMixedHomotopy
public import Colib.Topology.Realization.HomotopyNaturality

/-! Implementation provenance: `Quillen/Waldhausen/Additivity/MixedTransformationSquare.lean` at
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

variable (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X))

/-- The entire zero-cut transformation track realizes on the unchanged ordinary diagonal. -/
theorem normalizedMixedTransformationRealizationHomotopy_zero (t : unitInterval)
    (y : |SSet.diagonalSSet (bisimplicialSSet V)|) :
    realizationSimplicialHomotopy
      (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (t, SSet.toTop.map (SSet.diagonalMap (outerZeroSection (bisimplicialSSet V))) y) =
    realizationSimplicialHomotopy
      (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (t, y) := by
  simpa only [CategoryTheory.Functor.map_id, TopCat.id_app] using
    realizationSimplicialHomotopy_naturality
      (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (SSet.diagonalMap (outerZeroSection (bisimplicialSSet V))) (𝟙 _)
      (by simpa only [Category.comp_id] using
        (normalizedMixedTransformationHomotopy_zero V W a a' b b' hs hs'
          ηF ηG haη hηF hηG)) t y

/-- The actual two-time realization. The tuple order is transformation, mixed, then native input. -/
def normalizedMixedTransformationRealizationSquare :
    C(unitInterval × (unitInterval ×
      |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|),
      |SSet.diagonalSSet (bisimplicialSSet W)|) where
  toFun z := realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (z.1, realizationSimplicialHomotopy (outerContraction (bisimplicialSSet V))
        (z.2.1, SSet.toTop.map
          (SSet.diagonalMap (outerOneSection (bisimplicialSSet V))) z.2.2))
  continuous_toFun :=
    (realizationSimplicialHomotopy
      (normalizedMixedTransformationHomotopy V W a a' b b' hs hs'
        ηF ηG haη hηF hηG)).continuous.comp
      (continuous_fst.prodMk
        ((realizationSimplicialHomotopy (outerContraction (bisimplicialSSet V))).continuous.comp
          ((continuous_fst.comp continuous_snd).prodMk
            ((SSet.toTop.map
              (SSet.diagonalMap (outerOneSection (bisimplicialSSet V)))).hom.continuous.comp
                (continuous_snd.comp continuous_snd)))))

/-- The full two-time map is the realization of the literal square through the two original
inverse cylinder isomorphisms, without a global product-realization inverse. -/
theorem normalizedMixedTransformationRealizationSquare_apply (t s : unitInterval)
    (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (t, (s, x)) =
      SSet.toTop.map
        (normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG)
        ((realizationCylinderIso
          (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1])).inv
          ((realizationCylinderIso
            (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V))).inv
              (x, ULift.up s), ULift.up t)) := by
  let p := (realizationCylinderIso
    (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V))).inv
      (x, ULift.up s)
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality
      (SSet.diagonalMap (outerOneSection (bisimplicialSSet V)))) (x, ULift.up s)
  change SSet.toTop.map
    (SSet.diagonalMap (outerOneSection (bisimplicialSSet V)) ▷ Δ[1]) p =
      (realizationCylinderIso (SSet.diagonalSSet (outerCylinder (bisimplicialSSet V)))).inv
        (SSet.toTop.map (SSet.diagonalMap (outerOneSection (bisimplicialSSet V))) x,
          ULift.up s) at hn
  have hi : realizationSimplicialHomotopy (outerContraction (bisimplicialSSet V))
      (s, SSet.toTop.map (SSet.diagonalMap (outerOneSection (bisimplicialSSet V))) x) =
        SSet.toTop.map (mixedTransformationInputCylinder V) p := by
    change SSet.toTop.map (outerContraction (bisimplicialSSet V)).h _ = _
    rw [← hn, mixedTransformationInputCylinder, Functor.map_comp, TopCat.comp_app]
  have ho := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (mixedTransformationInputCylinder V)) (p, ULift.up t)
  change SSet.toTop.map (mixedTransformationInputCylinder V ▷ Δ[1])
      ((realizationCylinderIso
        (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1])).inv
          (p, ULift.up t)) =
    (realizationCylinderIso (SSet.diagonalSSet (outerCylinder (bisimplicialSSet V)))).inv
      (SSet.toTop.map (mixedTransformationInputCylinder V) p, ULift.up t) at ho
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [hi]
  change SSet.toTop.map
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h _ = _
  rw [← ho, normalizedMixedTransformationSquare, Functor.map_comp, TopCat.comp_app]

/-- Transformation time zero is the entire old normalized mixed realization. -/
theorem normalizedMixedTransformationRealizationSquare_transformation_zero (s : unitInterval)
    (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (0, (s, x)) =
      realizationSimplicialHomotopy
        (normalizedMixedEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration) (s, x) := by
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [ContinuousMap.Homotopy.apply_zero]
  exact realizationSimplicialHomotopy_naturality
    (outerContraction (bisimplicialSSet V))
    (normalizedMixedEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration)
    (SSet.diagonalMap (outerOneSection (bisimplicialSSet V)))
    (SSet.diagonalMap (normalizedMixedMap V W a hs.exactF hs.exactG hs.cofibration))
    rfl s x

/-- Transformation time one is the entire primed old normalized mixed realization. -/
theorem normalizedMixedTransformationRealizationSquare_transformation_one (s : unitInterval)
    (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (1, (s, x)) =
      realizationSimplicialHomotopy
        (normalizedMixedEndpointHomotopy V W a' hs'.exactF hs'.exactG hs'.cofibration) (s, x) := by
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [ContinuousMap.Homotopy.apply_one]
  exact realizationSimplicialHomotopy_naturality
    (outerContraction (bisimplicialSSet V))
    (normalizedMixedEndpointHomotopy V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (SSet.diagonalMap (outerOneSection (bisimplicialSSet V)))
    (SSet.diagonalMap (normalizedMixedMap V W a' hs'.exactF hs'.exactG hs'.cofibration))
    rfl s x

/-- Mixed time zero is the full identity-endpoint transformation on actual horizontal
restriction. -/
theorem normalizedMixedTransformationRealizationSquare_mixed_zero (t : unitInterval)
    (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (t, (0, x)) =
      realizationSimplicialHomotopy
        (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
        (t, SSet.toTop.map
          (SSet.diagonalMap
            (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))) x) := by
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [ContinuousMap.Homotopy.apply_zero]
  have hp := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ SSet.toTop.map (SSet.diagonalMap f))
      (outerOneSection_projection (bisimplicialSSet V))) x
  change (SSet.diagonalFunctor ⋙ SSet.toTop).map
    (outerOneSection (bisimplicialSSet V) ≫ outerProjection (bisimplicialSSet V)) x = _ at hp
  rw [Functor.map_comp, TopCat.comp_app] at hp
  change SSet.toTop.map (SSet.diagonalMap (outerProjection (bisimplicialSSet V)))
      (SSet.toTop.map (SSet.diagonalMap (outerOneSection (bisimplicialSSet V))) x) = _ at hp
  rw [SSet.toTop.map_comp]
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (t, SSet.toTop.map (SSet.diagonalMap (outerZeroSection (bisimplicialSSet V))) _) = _
  refine (congrArg (fun y ↦ realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
      (t, SSet.toTop.map (SSet.diagonalMap (outerZeroSection (bisimplicialSSet V))) y))
        hp).trans ?_
  exact normalizedMixedTransformationRealizationHomotopy_zero V W a a' b b' hs hs'
    ηF ηG haη hηF hηG t _

/-- Mixed time one is the full unchanged separated-endpoint transformation. -/
theorem normalizedMixedTransformationRealizationSquare_mixed_one (t : unitInterval)
    (x : |SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (t, (1, x)) =
      realizationSimplicialHomotopy
        (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
        (t, x) := by
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [ContinuousMap.Homotopy.apply_one, SSet.toTop.map_id]
  change realizationSimplicialHomotopy
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (t, SSet.toTop.map (SSet.diagonalMap (outerOneSection (bisimplicialSSet V))) x) = _
  simpa only [CategoryTheory.Functor.map_id, TopCat.id_app] using
    realizationSimplicialHomotopy_naturality
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG)
    (SSet.diagonalMap (outerOneSection (bisimplicialSSet V))) (𝟙 _)
    (by simpa only [Category.comp_id] using
      normalizedMixedTransformationHomotopy_one V W a a' b b' hs hs' ηF ηG haη hηF hηG) t x

/-- Both full continuous times fix the actual subdivided zero input. -/
theorem normalizedMixedTransformationRealizationSquare_fixed_zero (t s : unitInterval) :
    normalizedMixedTransformationRealizationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
        (t, (s, subdivisionBasepoint V)) = realizationPoint (diagonalZeroVertex W) := by
  rw [normalizedMixedTransformationRealizationSquare_apply]
  let p := (realizationCylinderIso (Δ[0] : SSet.{max u v})).inv (default, ULift.up s)
  let z := (realizationCylinderIso (Δ[0] ⊗ Δ[1] : SSet.{max u v})).inv (p, ULift.up t)
  have hi := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (SSet.yonedaEquiv.symm (subdivisionZeroVertex V)))
    (default, ULift.up s)
  change SSet.toTop.map (SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) p =
    (realizationCylinderIso
      (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V))).inv
      (subdivisionBasepoint V, ULift.up s) at hi
  have ho := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality
      (SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1])) (p, ULift.up t)
  change SSet.toTop.map
    ((SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) z =
      (realizationCylinderIso
        (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1])).inv
        (SSet.toTop.map (SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) p,
          ULift.up t) at ho
  change SSet.toTop.map
    (normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG) _ = _
  rw [← hi, ← ho]
  change (SSet.toTop.map ((SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) ≫
    SSet.toTop.map
      (normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG)) z = _
  rw [← Functor.map_comp, normalizedMixedTransformationSquare_fixed_zero,
    Functor.map_comp, Functor.map_comp]
  change SSet.toTop.map (SSet.yonedaEquiv.symm (diagonalZeroVertex W)) _ = _
  exact congrArg (fun y : |(Δ[0] : SSet.{max u v})| ↦
    SSet.toTop.map (SSet.yonedaEquiv.symm (diagonalZeroVertex W)) y)
      (Subsingleton.elim _ default)


end CategoryTheory.Waldhausen.Additivity

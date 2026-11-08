/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.ChangeWeakMixedHomotopy
public import Colib.KTheory.Waldhausen.Additivity.NormalizedMixedHomotopy
public import Colib.Topology.Realization.HomotopyNaturality

/-!
# The original mixed additivity track under fine-to-coarse comparison

The actual cylinder equation descends to the unchanged realization homotopy at every point
and time. This treats the mixed part of the based additivity pasting; its two endpoint
homotopies and the final localization-boundary comparison are separate obligations.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Additivity/ChangeWeakMixedHomotopy.lean:57-76`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native ownership preserves the
actual chosen zero, normalizations, cylinder coordinates, maps and orientations. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SSet.MixedOrdinalCylinder
open SSet
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (N : Fibration.NestedWeakEquivalences W)
  {F G : C ⥤ D} (a : F ⟶ G)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hc : IsCofibrationTransformation W a V)

/-- Both original realization parameters survive the actual fine-to-coarse comparison. -/
theorem normalizedMixedRealizationHomotopy_changeWeak (t : unitInterval)
    (x : |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    SSet.toTop.map (SSet.diagonalMap
      (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
        (realizationSimplicialHomotopy
          (normalizedMixedEndpointHomotopy V W a hF hG hc) (t, x)) =
      realizationSimplicialHomotopy
        (normalizedMixedEndpointHomotopy V N.coarse a
          (hF.comp (Fibration.changeWeak_exact N))
          (hG.comp (Fibration.changeWeak_exact N))
          (isCofibrationTransformation_changeWeak V W N a hc)) (t, x) := by
  simpa using realizationSimplicialHomotopy_naturality
    (normalizedMixedEndpointHomotopy V W a hF hG hc)
    (normalizedMixedEndpointHomotopy V N.coarse a
      (hF.comp (Fibration.changeWeak_exact N))
      (hG.comp (Fibration.changeWeak_exact N))
      (isCofibrationTransformation_changeWeak V W N a hc))
    (𝟙 _) (SSet.diagonalMap
      (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
    (by simpa using normalizedMixedEndpointHomotopy_changeWeak V W N a hF hG hc) t x


end CategoryTheory.Waldhausen.Additivity

attribute [colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/ChangeWeakMixedHomotopy.lean:57-76"
    "adaptation" "Every actual time and input of the realized mixed cylinder"]
  CategoryTheory.Waldhausen.Additivity.normalizedMixedRealizationHomotopy_changeWeak

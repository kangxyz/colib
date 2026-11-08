/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.ChangeWeakDeformation
public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedMixedHomotopy

/-!
# The original mixed additivity track under fine-to-coarse comparison

The actual cylinder equation descends to the unchanged realization homotopy at every point
and time. This treats the mixed part of the based additivity pasting; its two endpoint
homotopies and the final localization-boundary comparison are separate obligations.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Additivity/ChangeWeakMixedHomotopy.lean:36-54`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native ownership preserves the
actual chosen zero, normalizations, cylinder coordinates, maps and orientations. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SSet.MixedOrdinalCylinder
open SSet
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (N : Fibration.NestedWeakEquivalences W)
  {F G : C ⥤ D} (a : F ⟶ G)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hc : IsCofibrationTransformation W a V)

/-- Fine-to-coarse comparison preserves the exact original mixed simplicial cylinder. -/
theorem normalizedMixedEndpointHomotopy_changeWeak :
    (normalizedMixedEndpointHomotopy V W a hF hG hc).h ≫
        SSet.diagonalMap
          (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)) =
      (normalizedMixedEndpointHomotopy V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc)).h := by
  have h := congrArg (fun k =>
    SSet.diagonalMap (outerOneSection (bisimplicialSSet V)) ▷ Δ[1] ≫
      (outerContraction (bisimplicialSSet V)).h ≫ SSet.diagonalMap k)
    (normalizedMixedMap_changeWeak V W N a hF hG hc)
  have hd := SSet.diagonalFunctor.map_comp (normalizedMixedMap V W a hF hG hc)
    (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N))
  change SSet.diagonalMap (_ ≫ _) =
    SSet.diagonalMap _ ≫ SSet.diagonalMap _ at hd
  rw [hd] at h
  simpa only [normalizedMixedEndpointHomotopy, mixedEndpointHomotopy,
    Category.assoc] using h


end CategoryTheory.Waldhausen.Additivity

attribute [colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/ChangeWeakMixedHomotopy.lean:36-54"
    "adaptation" "The original minimum-cut simplicial cylinder under weak enlargement"]
  CategoryTheory.Waldhausen.Additivity.normalizedMixedEndpointHomotopy_changeWeak

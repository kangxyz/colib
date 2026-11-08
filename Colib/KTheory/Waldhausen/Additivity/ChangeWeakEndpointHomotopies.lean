/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.ChangeWeakEndpointHomotopies
public import Colib.KTheory.Waldhausen.Additivity.NormalizedEndpointHomotopies
public import Colib.Topology.Realization.HomotopyNaturality

/-!
# Original additivity endpoint tracks under weak enlargement

The same structural cofibration sequence and original normalization isomorphisms give the
literal fine-to-coarse squares for both endpoint cylinders.
-/
/-! Implementation provenance:
  `Quillen/Waldhausen/Additivity/ChangeWeakEndpointHomotopies.lean:49-68, 103-118`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native ownership preserves the
actual chosen zero, normalizations, cylinder coordinates, maps and orientations. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open SSet
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (N : Fibration.NestedWeakEquivalences W)
  {F G H : C ⥤ D} (a : F ⟶ G)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hc : IsCofibrationTransformation W a V)

/-- The original realized identity-endpoint track commutes at every time and point. -/
theorem normalizedIdentityEndpointRealizationHomotopy_changeWeak (t : unitInterval)
    (x : |SSet.diagonalSSet (bisimplicialSSet V)|) :
    SSet.toTop.map (SSet.diagonalMap
      (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
        (normalizedIdentityEndpointRealizationHomotopy V W a hF hG hc (t, x)) =
      normalizedIdentityEndpointRealizationHomotopy V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc) (t, x) := by
  simpa only [normalizedIdentityEndpointRealizationHomotopy,
    CategoryTheory.Functor.map_id, TopCat.id_app] using
    realizationSimplicialHomotopy_naturality
      (normalizedIdentityEndpointHomotopy V W a hF hG hc)
      (normalizedIdentityEndpointHomotopy V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc))
      (𝟙 _) (SSet.diagonalMap
        (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
      (by simpa using normalizedIdentityEndpointHomotopy_changeWeak V W N a hF hG hc) t x

variable [HasBinaryCoproducts D] (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

/-- Every point of the original separated realization track is preserved. -/
theorem normalizedSeparatedEndpointRealizationHomotopy_changeWeak (t : unitInterval)
    (x : |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    SSet.toTop.map (SSet.diagonalMap
      (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
        (normalizedSeparatedEndpointRealizationHomotopy V W a b hs (t, x)) =
      normalizedSeparatedEndpointRealizationHomotopy V N.coarse a b
        (isCofibrationSequence_changeWeak V W N a b hs) (t, x) := by
  simpa only [normalizedSeparatedEndpointRealizationHomotopy,
    CategoryTheory.Functor.map_id, TopCat.id_app] using
    realizationSimplicialHomotopy_naturality
      (normalizedSeparatedEndpointHomotopy V W a b hs)
      (normalizedSeparatedEndpointHomotopy V N.coarse a b
        (isCofibrationSequence_changeWeak V W N a b hs))
      (𝟙 _) (SSet.diagonalMap
        (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)))
      (by simpa using normalizedSeparatedEndpointHomotopy_changeWeak V W N a b hs) t x


end CategoryTheory.Waldhausen.Additivity

attribute [colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/ChangeWeakEndpointHomotopies.lean:49-118"
    "adaptation" "Whole identity and quotient-first endpoint realization tracks"]
  CategoryTheory.Waldhausen.Additivity.normalizedIdentityEndpointRealizationHomotopy_changeWeak
  CategoryTheory.Waldhausen.Additivity.normalizedSeparatedEndpointRealizationHomotopy_changeWeak

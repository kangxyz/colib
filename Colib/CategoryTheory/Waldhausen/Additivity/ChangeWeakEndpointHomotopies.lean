/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.ChangeWeakDeformation
public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedEndpointHomotopies

/-!
# Original additivity endpoint tracks under weak enlargement

The same structural cofibration sequence and original normalization isomorphisms give the
literal fine-to-coarse squares for both endpoint cylinders.
-/
/-! Implementation provenance:
  `Quillen/Waldhausen/Additivity/ChangeWeakEndpointHomotopies.lean:34-46, 70-100`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native ownership preserves the
actual chosen zero, normalizations, cylinder coordinates, maps and orientations. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open SSet
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (N : Fibration.NestedWeakEquivalences W)
  {F G H : C ⥤ D} (a : F ⟶ G)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hc : IsCofibrationTransformation W a V)

/-- The identity-endpoint cylinder retains the actual normalization and comparison maps. -/
theorem normalizedIdentityEndpointHomotopy_changeWeak :
    (normalizedIdentityEndpointHomotopy V W a hF hG hc).h ≫
        SSet.diagonalMap
          (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)) =
      (normalizedIdentityEndpointHomotopy V N.coarse a
        (hF.comp (Fibration.changeWeak_exact N))
        (hG.comp (Fibration.changeWeak_exact N))
        (isCofibrationTransformation_changeWeak V W N a hc)).h := by
  cases W
  rcases N with ⟨coarse, hcof, hzero, hw⟩
  cases coarse
  cases hzero
  rfl

variable (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

include hs in
/-- The unchanged actual cofiber squares give a cofibration sequence in the coarse structure. -/
theorem isCofibrationSequence_changeWeak : IsCofibrationSequence V N.coarse a b where
  exactF := hs.exactF.comp (Fibration.changeWeak_exact N)
  exactG := hs.exactG.comp (Fibration.changeWeak_exact N)
  exactH := hs.exactH.comp (Fibration.changeWeak_exact N)
  cofibration := isCofibrationTransformation_changeWeak V W N a hs.cofibration
  cofiber X := by
    have h := hs.cofiber X
    cases W
    rcases N with ⟨coarse, hcof, hzero, hw⟩
    cases coarse
    cases hzero
    exact h

variable [HasBinaryCoproducts D]

/-- The separated endpoint keeps the original cofiber and normalized split comparison. -/
theorem normalizedSeparatedEndpointHomotopy_changeWeak :
    (normalizedSeparatedEndpointHomotopy V W a b hs).h ≫
        SSet.diagonalMap
          (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N)) =
      (normalizedSeparatedEndpointHomotopy V N.coarse a b
        (isCofibrationSequence_changeWeak V W N a b hs)).h := by
  cases W
  rcases N with ⟨coarse, hcof, hzero, hw⟩
  cases coarse
  cases hzero
  rfl


end CategoryTheory.Waldhausen.Additivity

attribute [colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/ChangeWeakEndpointHomotopies.lean:34-100"
    "adaptation" "Original identity and quotient-first simplicial endpoint cylinders"]
  CategoryTheory.Waldhausen.Additivity.normalizedIdentityEndpointHomotopy_changeWeak
  CategoryTheory.Waldhausen.Additivity.isCofibrationSequence_changeWeak
  CategoryTheory.Waldhausen.Additivity.normalizedSeparatedEndpointHomotopy_changeWeak

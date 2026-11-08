/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Additivity.ChangeWeakEndpointHomotopies
public import Colib.KTheory.Waldhausen.Additivity.ChangeWeakMixedHomotopy
public import Colib.KTheory.Waldhausen.Additivity.SubdividedBasedHomotopy

/-!
# The specified based additivity track under fine-to-coarse comparison

All three original tracks are transported, retaining their original concatenation and reversal
parameters. This is naturality of the specified subdivided based deformation.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Additivity/ChangeWeakBasedHomotopy.lean:26-65`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native ownership preserves the
actual chosen zero, normalizations, cylinder coordinates, maps and orientations. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open SSet
open scoped Simplicial Topology
universe u v u₁ u₂ u₃
namespace CategoryTheory.Waldhausen.Additivity

private theorem homotopyRel_trans_map
    {X : Type u₁} {Y : Type u₂} {Z : Type u₃}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f₀ f₁ f₂ : C(X, Y)} {g₀ g₁ g₂ : C(X, Z)} {S : Set X}
    (b : C(Y, Z)) (H : f₀.HomotopyRel f₁ S) (K : f₁.HomotopyRel f₂ S)
    (H' : g₀.HomotopyRel g₁ S) (K' : g₁.HomotopyRel g₂ S)
    (hH : ∀ t x, b (H (t, x)) = H' (t, x))
    (hK : ∀ t x, b (K (t, x)) = K' (t, x)) (t : unitInterval) (x : X) :
    b ((H.trans K) (t, x)) = (H'.trans K') (t, x) := by
  simp only [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · exact hH _ _
  · exact hK _ _

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (N : Fibration.NestedWeakEquivalences W)
  [HasBinaryCoproducts D] {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
  (hs : IsCofibrationSequence V W a b)

/-- Fine-to-coarse comparison retains the whole original based additivity deformation. -/
theorem subdividedBasedAdditivityHomotopy_changeWeak (t : unitInterval)
    (x : |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    realizedDiagonalMap (bisimplicialSSetMap W.cof W.weq (Fibration.changeWeak_exact N))
        (subdividedBasedAdditivityHomotopy V W a b hs (t, x)) =
      subdividedBasedAdditivityHomotopy V N.coarse a b
        (isCofibrationSequence_changeWeak V W N a b hs) (t, x) := by
  unfold subdividedBasedAdditivityHomotopy
  apply homotopyRel_trans_map
  · intro s y
    exact normalizedIdentityEndpointRealizationHomotopy_changeWeak V W N a
      hs.exactF hs.exactG hs.cofibration (unitInterval.symm s)
      (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) y)
  · intro s y
    apply homotopyRel_trans_map
    · intro r z
      exact normalizedMixedRealizationHomotopy_changeWeak V W N a
        hs.exactF hs.exactG hs.cofibration r z
    · intro r z
      exact normalizedSeparatedEndpointRealizationHomotopy_changeWeak V W N a b hs r z

end CategoryTheory.Waldhausen.Additivity

attribute [colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/ChangeWeakBasedHomotopy.lean:46-65"
    "adaptation" "The entire specified three-stage based additivity track"]
  CategoryTheory.Waldhausen.Additivity.subdividedBasedAdditivityHomotopy_changeWeak

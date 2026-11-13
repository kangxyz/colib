/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.MorphismProperty
import Colib.Topology.Realization.CoproductHomotopy
import Colib.Topology.Realization.WeakHomotopyEquiv

/-!
# Realization weak equivalences of coproducts

The disjoint-union homeomorphism of realizations identifies the actual
coproduct map with the disjoint union of the original realized maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace SSet

/-- The original coproduct map of realization weak equivalences is weak. -/
theorem IsRealizationWeakEquivalence.sigmaMap {ι : Type u} {X Y : ι → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, IsRealizationWeakEquivalence (f i)) :
    IsRealizationWeakEquivalence (Limits.Sigma.map f) := by
  let eX := (coproductIsCoproduct X).coconePointUniqueUpToIso (simplicialSigmaIsColimit X)
  let eY := (coproductIsCoproduct Y).coconePointUniqueUpToIso (simplicialSigmaIsColimit Y)
  have hX (i : ι) : Limits.Sigma.ι X i ≫ eX.hom = simplicialSigmaι X i :=
    (coproductIsCoproduct X).comp_coconePointUniqueUpToIso_hom _ ⟨i⟩
  have hY (i : ι) : Limits.Sigma.ι Y i ≫ eY.hom = simplicialSigmaι Y i :=
    (coproductIsCoproduct Y).comp_coconePointUniqueUpToIso_hom _ ⟨i⟩
  apply IsRealizationWeakEquivalence.of_iso_square _ (simplicialSigmaMap f) eX eY
  · apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, hY, ← Category.assoc, hX,
      simplicialSigmaι_map]
  · let E := realizationSigmaHomotopyEquiv (fun i => (hf i).homotopyEquiv)
    change Topology.IsWeakHomotopyEquivalence (SSet.toTop.map (simplicialSigmaMap f)).hom
    rw [← realizationSigmaHomotopyEquiv_toFun f (fun i => (hf i).homotopyEquiv)
      (fun i => (hf i).homotopyEquiv_toFun)]
    exact Topology.isWeakHomotopyEquivalence_of_homotopyEquiv E

instance realizationWeakEquivalences_isStableUnderCoproducts :
    realizationWeakEquivalences.{u}.IsStableUnderCoproducts.{u} where
  isStableUnderCoproductsOfShape ι :=
    .mk _ ι (fun _ _ _ _ f hf => IsRealizationWeakEquivalence.sigmaMap f hf)

end SSet

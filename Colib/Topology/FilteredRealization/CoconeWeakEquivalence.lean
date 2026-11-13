/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.FilteredRealization.HomotopyEquivalence
public import Colib.Topology.Realization.WeakHomotopyEquiv

/-!
# Realization weak equivalences into filtered colimits

If the transitions are realization weak equivalences, each cocone leg is
a realization weak equivalence. The comparison uses the original colimit
maps and applies to empty simplicial sets as well.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Topology.FilteredRealization

/-- Each original leg of a filtered colimit of realization weak equivalences is weak. -/
theorem isRealizationWeakEquivalence_coconeLeg
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (h : ∀ {i j : J} (f : i ⟶ j), SSet.IsRealizationWeakEquivalence (F.map f)) (j : J) :
    SSet.IsRealizationWeakEquivalence (c.ι.app j) := by
  let e := stageHomotopyEquiv F c hc (fun f => (h f).homotopyEquiv)
    (fun f => (h f).homotopyEquiv_toFun) j
  change IsWeakHomotopyEquivalence (SSet.toTop.map (c.ι.app j)).hom
  exact isWeakHomotopyEquivalence_of_homotopyEquiv e

end Topology.FilteredRealization

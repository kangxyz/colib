/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StableShift
public import Colib.Topology.Prespectrum.StableEquivalence

/-!
# Stable equivalence of the original parameter-correct loop map

Naturality of the proved signed stable loop shift conjugates the actual parameterLoopingMap
stable homomorphism to the original map in degree d+1. Thus original stable equivalences remain
stable after actual parameter looping, without levelwise weakness or an Omega hypothesis.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/ParameterLoopingStableEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual parameter-looped map is conjugated by the existing signed stable
shift in every integer degree, without a levelwise weakness or Omega premise. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- Actual parameter looping preserves original stable equivalences in every signed degree. -/
theorem parameterLoopingMap_isStableEquivalence {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : IsStableEquivalence f) : IsStableEquivalence (parameterLoopingMap f) := by
  intro d
  let := hf (d + 1)
  have he : (stableHomotopyFunctor d).map (parameterLoopingMap f) =
      (parameterStableHomotopyIso E d).hom ≫ (stableHomotopyFunctor (d + 1)).map f ≫
        (parameterStableHomotopyIso F d).inv := by
    apply (cancel_mono (parameterStableHomotopyIso F d).hom).1
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact parameterStableHomotopyIso_naturality f d
  rw [he]
  infer_instance

end Topology.LoopPrespectrum

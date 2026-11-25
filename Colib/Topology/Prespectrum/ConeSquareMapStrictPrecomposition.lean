/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ConeHomotopySquare
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# Strict precomposition of an original square-cone map

A strict arrow square preserves the entire cone height. Precomposing a square-cone map by
that actual strict cone map therefore retains precisely its original homotopy half and its
original cone half. No extra constant half or replacement square-cone map is inserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F E' F' E'' F'' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (h : E'' ⟶ F'')
  (sq : Arrow.mk f ⟶ Arrow.mk g) (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (g ≫ d) (c ≫ h))

/-- The unchanged original square track after the literal strict source input. -/
def mappingConeSquareStrictPrecompTrack :
    Homotopy (f ≫ (sq.right ≫ d)) ((sq.left ≫ c) ≫ h) :=
  (Homotopy.precomp sq.left H).cast
    (by
      have hw : sq.left ≫ g = f ≫ sq.right := sq.w
      exact (Category.assoc sq.left g d).symm.trans
        ((congrArg (fun k => k ≫ d) hw).trans (Category.assoc f sq.right d)))
    (Category.assoc sq.left c h).symm

/-- Strict precomposition preserves the original whole square-cone map literally. -/
theorem mappingConeMap_comp_squareMap :
    mappingConeMap sq ≫ mappingConeSquareMap g h c d H =
      mappingConeSquareMap f h (sq.left ≫ c) (sq.right ≫ d)
        (mappingConeSquareStrictPrecompTrack f g h sq c d H) := by
  apply mappingCone_hom_ext f
  · apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl
  · intro n s x
    rfl

end Topology.LoopPrespectrum

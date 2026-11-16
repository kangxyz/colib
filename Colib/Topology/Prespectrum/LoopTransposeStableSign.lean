/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.LoopTranspose
public import Colib.Topology.Prespectrum.StableShift
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.TransposeSign

/-!
# The original double-loop transpose acts by minus one stably

The existing coordinate-transposition calculation applies at each original
stable stage. Passing through the unchanged colimit proves the sign in every
integer degree, without identifying any geometric parameter permutation.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace Topology.LoopPrespectrum.LoopTranspose

/-- Each positive homotopy group of the actual double-loop transpose sees inversion. -/
theorem transpose_pi (E : LoopPrespectrum.{u}) (n k : ℕ)
    (a : HomotopyGroup.Pi (k + 2)
      ((parameterLooping (parameterLooping E)).space n)
      ((parameterLooping (parameterLooping E)).point n)) :
    HomotopyGroup.map ((transpose E).map n) ((transpose E).map_point n) a = a⁻¹ := by
  apply (loopShiftMulEquiv (x := Path.refl (E.point n)) (k + 1)).symm.injective
  apply (loopShiftMulEquiv (x := E.point n) (k + 2)).symm.injective
  rw [map_inv, map_inv]
  exact loopShiftEquiv_twice_coordinateSwap (k + 2) (Path.doubleLoopTranspose (E.point n))
    (Path.doubleLoopTranspose_refl _) (fun _ _ _ => rfl) a

/-- Every original stable-stage map is the negative identity, with no tail reindexing. -/
theorem stableSystemMap_transpose (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) :
    (stableSystemMap (transpose E) d).app n =
      -𝟙 ((stableSystem (parameterLooping (parameterLooping E)) d).obj n) := by
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul
    (transpose_pi E ((-d).toNat + n + 2) (d.toNat + n) (Additive.toMul a))

/-- The actual double-loop transpose induces minus identity in every signed stable degree. -/
theorem stableHomotopyFunctor_map_transpose (E : LoopPrespectrum.{u}) (d : ℤ) :
    (stableHomotopyFunctor d).map (transpose E) =
      -𝟙 (stableHomotopyGroup (parameterLooping (parameterLooping E)) d) := by
  apply colimit.hom_ext
  intro n
  change stableHomotopyι _ d n ≫ (stableHomotopyFunctor d).map (transpose E) =
    stableHomotopyι _ d n ≫ (-𝟙 _)
  rw [stableHomotopyι_naturality, stableSystemMap_transpose]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp,
    Category.comp_id]

end Topology.LoopPrespectrum.LoopTranspose

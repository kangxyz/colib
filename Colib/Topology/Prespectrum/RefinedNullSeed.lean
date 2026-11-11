/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.NullLoopNaturality
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.ZeroHomComposition

/-!
# Seeds from independent cells under an actual target refinement

An independently supplied cell is included into the refined cone and conjugated
by the image of the original whole null. A proved whole-cell comparison gives
the exact original seed followed by the looped refinement. Neither the seed nor
its null is defined by transporting a stable class.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.RefinedNullSeed
variable {E D C D' C' : LoopPrespectrum.{u}} (f : E ⟶ D) (j : D ⟶ C)
  (r : D ⟶ D') (s : C ⟶ C') (j' : D' ⟶ C') (h : r ≫ j' = j ≫ s)
  (K : Homotopy (f ≫ r) (f ≫ r)) (N : Homotopy (f ≫ j) (zeroHom E C))

/-- The independent cell is followed by the actual refined inclusion. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RefinedNullSeed.lean:30"
  "adaptation" "Original whole-null refinement and normalized boundary comparison"]
def cell : Homotopy ((f ≫ j) ≫ s) ((f ≫ j) ≫ s) :=
  (K.postcomp j').cast
    (by rw [Category.assoc, h, Category.assoc])
    (by rw [Category.assoc, h, Category.assoc])

/-- The full original null is retained under the actual refinement map. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RefinedNullSeed.lean:36"
  "adaptation" "Original whole-null refinement and normalized boundary comparison"]
def null : Homotopy ((f ≫ j) ≫ s) (zeroHom E C') :=
  (N.postcomp s).cast rfl (zeroHom_comp s)

/-- The independent cell and original null give the actual null-conjugated refined seed. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RefinedNullSeed.lean:40"
  "adaptation" "Original whole-null refinement and normalized boundary comparison"]
def seed : E ⟶ parameterLooping C' :=
  (cell f j r s j' h K).nullLoopMap (null f j s N)

/-- A whole-cell comparison identifies the entire seed map with its original postcomposite. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RefinedNullSeed.lean:44"
  "adaptation" "Original whole-null refinement and normalized boundary comparison"]
theorem seed_eq (H : Homotopy f f) (hK : K = H.postcomp r) :
    seed f j r s j' h K N = (H.postcomp j).nullLoopMap N ≫ parameterLoopingMap s := by
  have hh := Homotopy.nullLoopMap_naturality (𝟙 E) s (H.postcomp j)
    (cell f j r s j' h K) N (null f j s N)
  have hH : ∀ n, ((H.postcomp j).postcomp s).level n =
      (Homotopy.precomp (𝟙 E) (cell f j r s j' h K)).level n := by
    intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    subst K
    exact (congrArg (fun m : D ⟶ C' => m.map n (H.level n (t, x))) h).symm
  have hN : ∀ n, (N.postcomp s).level n =
      (Homotopy.precomp (𝟙 E) (null f j s N)).level n := by
    intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    rfl
  simpa only [seed, Category.id_comp] using (hh hH hN).symm

end Topology.LoopPrespectrum.RefinedNullSeed

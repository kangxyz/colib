/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Topology.Prespectrum.ConeMovingSquareLaws
public import Colib.Topology.Prespectrum.HomotopySquareComposition
public import Colib.Topology.Prespectrum.ConeHomotopySquare
public import Colib.Topology.Prespectrum.HomotopySquareBoundary
public import Colib.Topology.Prespectrum.HomotopySquareOfPasting

/-!
# Cone Square Map Composition

Composition of the exact original square-cone maps, retaining all three cylinder pieces.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F E' F' E'' F'' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (h : E'' ⟶ F'')
  (a : E ⟶ E') (b : F ⟶ F') (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))

/-- The whole two original square tracks, in their prescribed order. -/
def coneSquarePastedHomotopy : Homotopy (f ≫ (b ≫ d)) ((a ≫ c) ≫ h) :=
  ((H.postcomp d).trans ((Homotopy.precomp a K).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)).cast
      (Category.assoc _ _ _) rfl

/-- The full original composite cone cylinder, with its inclusion endpoints transported. -/
def coneSquareCompositeNullHomotopy :
    Homotopy (f ≫ ((b ≫ d) ≫ mappingConeInclusion h)) (zeroHom E (mappingCone h)) :=
  ((mappingConeSquareNullHomotopy f g a b H).postcomp
    (mappingConeSquareMap g h c d K)).cast
    (by simp only [Category.assoc, mappingConeSquareMap_inclusion]) (zeroHom_comp _)

/-- Literal descent recovers the exact composite of the original cone maps. -/
theorem coneSquareCompositeDesc :
    mappingConeDesc f ((b ≫ d) ≫ mappingConeInclusion h)
      (coneSquareCompositeNullHomotopy f g h a b c d H K) =
      mappingConeSquareMap f g a b H ≫ mappingConeSquareMap g h c d K := by
  apply mappingCone_hom_ext
  · simp only [mappingConeInclusion_desc, ← Category.assoc, mappingConeSquareMap_inclusion]
    simp only [Category.assoc, mappingConeSquareMap_inclusion]
  · intro n s x
    rfl

/-- Reassociation compares the pasted square-cone cylinder with the exact composite cylinder.
Only path parentheses change; none of the three original pieces is removed. -/
def coneSquareCompositionNullComparison :
    (mappingConeSquareNullHomotopy f h (a ≫ c) (b ≫ d)
      (coneSquarePastedHomotopy f g h a b c d H K)).RelHomotopy
      (coneSquareCompositeNullHomotopy f g h a b c d H K) := by
  let i := mappingConeInclusion h
  let A := H.postcomp (d ≫ i)
  let B : Homotopy ((a ≫ g) ≫ (d ≫ i)) ((a ≫ c) ≫ (h ≫ i)) :=
    (Homotopy.precomp a (K.postcomp i)).cast
      (by simp only [Category.assoc]) (by simp only [Category.assoc])
  let C := Homotopy.precomp (a ≫ c) (mappingConeHomotopy h)
  apply Homotopy.RelHomotopy.ofLevels (Homotopy.RelHomotopy.transAssoc A B C)
  · intro n
    apply Homotopy.trans_level_congr
    · change (((H.postcomp d).trans ((Homotopy.precomp a K).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)).postcomp i).level n =
        (A.trans B).level n
      rw [Homotopy.postcomp_trans]
      apply Homotopy.trans_level_congr <;> rfl
    · rfl
  · intro n
    change ((mappingConeSquareNullHomotopy f g a b H).postcomp
      (mappingConeSquareMap g h c d K)).level n = _
    rw [mappingConeSquareNullHomotopy, Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr
    · change (H.postcomp (mappingConeInclusion g ≫ mappingConeSquareMap g h c d K)).level n = _
      rw [mappingConeSquareMap_inclusion]
    · change (Homotopy.precomp a (mappingConeSquareNullHomotopy g h c d K)).level n = _
      rw [mappingConeSquareNullHomotopy, Homotopy.precomp_trans]
      apply Homotopy.trans_level_congr <;> rfl

/-- Actual square-cone composition holds up to the explicit complete cylinder reparameterization. -/
def coneSquareMapCompositionHomotopy :
    Homotopy
      (mappingConeSquareMap f h (a ≫ c) (b ≫ d)
        (coneSquarePastedHomotopy f g h a b c d H K))
      (mappingConeSquareMap f g a b H ≫ mappingConeSquareMap g h c d K) :=
  (mappingConeDescHomotopy f ((b ≫ d) ≫ mappingConeInclusion h)
    (coneSquareCompositionNullComparison f g h a b c d H K)).cast rfl
      (coneSquareCompositeDesc f g h a b c d H K)

end Topology.LoopPrespectrum

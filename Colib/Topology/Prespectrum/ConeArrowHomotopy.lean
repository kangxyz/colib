/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.ConeHomotopy
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty

/-!
# Changing the original cone arrow by a whole based homotopy

A specified homotopy between arrows with unchanged source and target induces a genuine map between
their existing cones. Reversal supplies its actual homotopy inverse. The proof retains the whole
track, reassociates its exact concatenation, and contracts it against its reversal relative to the
original endpoints. No inverse of a weak equivalence or point-set cofibration is assumed.
-/
@[expose] public section
noncomputable section

open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

variable {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F}

/-- The unchanged target inclusion followed by the whole supplied arrow track and cone cylinder. -/
def mappingConeHomotopyMap (H : Homotopy f g) : mappingCone f ⟶ mappingCone g :=
  mappingConeDesc f (mappingConeInclusion g)
    ((H.postcomp (mappingConeInclusion g)).trans (mappingConeHomotopy g))

@[simp] theorem mappingConeHomotopyMap_inclusion (H : Homotopy f g) :
    mappingConeInclusion f ≫ mappingConeHomotopyMap H = mappingConeInclusion g :=
  mappingConeInclusion_desc f _ _

/-- The original source cone cylinder maps to precisely the specified concatenated nullhomotopy. -/
theorem mappingConeHomotopyMap_nullHomotopy (H : Homotopy f g) :
    (mappingConeHomotopy f).postcomp (mappingConeHomotopyMap H) =
      (H.postcomp (mappingConeInclusion g)).trans (mappingConeHomotopy g) := by
  apply Homotopy.ext
  funext n
  ext z
  rfl

/-- Composition retains its actual right-associated three-part cylinder, including both tracks. -/
theorem mappingConeHomotopyMap_comp (H : Homotopy f g) (K : Homotopy g h) :
    mappingConeHomotopyMap H ≫ mappingConeHomotopyMap K =
      mappingConeDesc f (mappingConeInclusion h)
        ((H.postcomp (mappingConeInclusion h)).trans
          ((K.postcomp (mappingConeInclusion h)).trans (mappingConeHomotopy h))) := by
  apply mappingCone_hom_ext
  · apply Hom.ext
    funext n
    ext y
    rfl
  · intro n s x
    have he :
        (((H.postcomp (mappingConeInclusion g)).trans (mappingConeHomotopy g)).postcomp
          (mappingConeHomotopyMap K)) =
        (H.postcomp (mappingConeInclusion h)).trans
          ((K.postcomp (mappingConeInclusion h)).trans (mappingConeHomotopy h)) := by
      rw [Homotopy.postcomp_trans, mappingConeHomotopyMap_nullHomotopy]
      congr 1
    exact congrArg (fun J ↦ J.level n (s, x)) he

/-- The actual three-part nullhomotopy contracts by reassociation and cancellation of its original
track against its reversal. -/
def mappingConeHomotopyMapCancelTrack (H : Homotopy f g) :
    ((H.postcomp (mappingConeInclusion f)).trans
      ((H.symm.postcomp (mappingConeInclusion f)).trans (mappingConeHomotopy f))).RelHomotopy
        (mappingConeHomotopy f) := by
  let L := H.postcomp (mappingConeInclusion f)
  have hsymm : H.symm.postcomp (mappingConeInclusion f) = L.symm :=
    Homotopy.postcomp_symm H (mappingConeInclusion f)
  rw [hsymm]
  exact (Homotopy.RelHomotopy.transAssoc L L.symm (mappingConeHomotopy f)).symm.trans
    (((Homotopy.RelHomotopy.reflTransSymm L).symm.hcomp
      (Homotopy.RelHomotopy.refl (mappingConeHomotopy f))).trans
        (Homotopy.RelHomotopy.reflTrans (mappingConeHomotopy f)))

/-- The homotopy supplied by reversing the arrow track is a genuine left inverse comparison. -/
def mappingConeHomotopyMapLeftHomotopy (H : Homotopy f g) :
    Homotopy (mappingConeHomotopyMap H ≫ mappingConeHomotopyMap H.symm) (𝟙 (mappingCone f)) :=
  (mappingConeDescHomotopy f (mappingConeInclusion f)
    (mappingConeHomotopyMapCancelTrack H)).cast
      (mappingConeHomotopyMap_comp H H.symm).symm (mappingConeDesc_self f)

/-- Reversing the same whole track gives the original right inverse comparison as well. -/
def mappingConeHomotopyMapRightHomotopy (H : Homotopy f g) :
    Homotopy (mappingConeHomotopyMap H.symm ≫ mappingConeHomotopyMap H) (𝟙 (mappingCone g)) := by
  simpa only [Homotopy.symm_symm] using mappingConeHomotopyMapLeftHomotopy H.symm

/-- Every actual level map changing the cone arrow by the supplied homotopy has its constructed
reverse-track homotopy inverse. -/
def mappingConeHomotopyMapLevelHomotopyEquiv (H : Homotopy f g) (n : ℕ) :
    ContinuousMap.HomotopyEquiv ((mappingCone f).space n) ((mappingCone g).space n) where
  toFun := (mappingConeHomotopyMap H).map n
  invFun := (mappingConeHomotopyMap H.symm).map n
  left_inv := ⟨((mappingConeHomotopyMapLeftHomotopy H).levelHomotopy n).toHomotopy⟩
  right_inv := ⟨((mappingConeHomotopyMapRightHomotopy H).levelHomotopy n).toHomotopy⟩

/-- The original whole-track arrow-change cone map is a complete weak equivalence on every level. -/
theorem mappingConeHomotopyMap_level_isWeakHomotopyEquivalence (H : Homotopy f g) (n : ℕ) :
    IsWeakHomotopyEquivalence ((mappingConeHomotopyMap H).map n) :=
  isWeakHomotopyEquivalence_of_homotopyEquiv (mappingConeHomotopyMapLevelHomotopyEquiv H n)

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/ConeArrowHomotopy.lean:1-113"
  "adaptation" "Actual whole-track descent and its original homotopy comparison"]
  mappingConeHomotopyMapLevelHomotopyEquiv

end Topology.LoopPrespectrum

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.PushoutHomotopy
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty

/-!
# Changing the original homotopy-pushout arrows along whole tracks

Changing either attaching arrow by a specified based homotopy gives an actual map of the original
reduced double cylinders. Reversing that same track supplies its homotopy inverse, through explicit
relative reassociation and cancellation. No point-set cofibration or weak-map inverse is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout

variable {A B C D : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- Descent of the original inclusions and the whole original overlap cylinder is the identity. -/
theorem desc_self : desc f g (inl f g) (inr f g) (glue f g) = 𝟙 (prespectrum f g) := by
  apply hom_ext
  · apply Hom.ext; funext n; ext y; rfl
  · apply Hom.ext; funext n; ext z; rfl
  · intro n s x; rfl

/-- Postcomposing the original cylinder with descent recovers every value of its supplied track. -/
theorem glue_desc (b : B ⟶ D) (c : C ⟶ D) (H : Homotopy (f ≫ b) (g ≫ c)) :
    (glue f g).postcomp (desc f g b c H) = H := by
  apply Homotopy.ext
  rfl

variable {f} {f' f'' : A ⟶ B} {g} {g' g'' : A ⟶ C}

/-- The original pushout map changing only its left attaching arrow along a whole track. -/
def leftHomotopyMap (H : Homotopy f f') (g : A ⟶ C) :
    prespectrum f g ⟶ prespectrum f' g :=
  desc f g (inl f' g) (inr f' g) ((H.postcomp (inl f' g)).trans (glue f' g))

/-- Left-arrow track composition retains its full right-associated cylinder parametrization. -/
theorem leftHomotopyMap_comp (H : Homotopy f f') (K : Homotopy f' f'') (g : A ⟶ C) :
    leftHomotopyMap H g ≫ leftHomotopyMap K g =
      desc f g (inl f'' g) (inr f'' g)
        ((H.postcomp (inl f'' g)).trans ((K.postcomp (inl f'' g)).trans (glue f'' g))) := by
  apply hom_ext
  · apply Hom.ext; funext n; ext y; rfl
  · apply Hom.ext; funext n; ext z; rfl
  · intro n s x
    have he : (((H.postcomp (inl f' g)).trans (glue f' g)).postcomp (leftHomotopyMap K g)) =
        (H.postcomp (inl f'' g)).trans ((K.postcomp (inl f'' g)).trans (glue f'' g)) := by
      rw [Homotopy.postcomp_trans]
      rw [show (glue f' g).postcomp (leftHomotopyMap K g) =
        (K.postcomp (inl f'' g)).trans (glue f'' g) from glue_desc _ _ _ _ _]
      congr 1
    exact congrArg (fun J ↦ J.level n (s, x)) he

/-- The actual doubled left-arrow track contracts relative to the unchanged endpoint maps. -/
def leftHomotopyMapCancelTrack (H : Homotopy f f') (g : A ⟶ C) :
    ((H.postcomp (inl f g)).trans
      ((H.symm.postcomp (inl f g)).trans (glue f g))).RelHomotopy (glue f g) := by
  let L := H.postcomp (inl f g)
  rw [show H.symm.postcomp (inl f g) = L.symm from Homotopy.postcomp_symm H (inl f g)]
  exact (Homotopy.RelHomotopy.transAssoc L L.symm (glue f g)).symm.trans
    (((Homotopy.RelHomotopy.reflTransSymm L).symm.hcomp
      (Homotopy.RelHomotopy.refl (glue f g))).trans (Homotopy.RelHomotopy.reflTrans (glue f g)))

/-- Reversing the same left-arrow track is a genuine left inverse comparison. -/
def leftHomotopyMapLeftHomotopy (H : Homotopy f f') (g : A ⟶ C) :
    Homotopy (leftHomotopyMap H g ≫ leftHomotopyMap H.symm g) (𝟙 (prespectrum f g)) :=
  (descHomotopy f g (inl f g) (inr f g) (leftHomotopyMapCancelTrack H g)).cast
    (leftHomotopyMap_comp H H.symm g).symm (desc_self f g)

/-- The actual left-arrow change map has the constructed reverse-track homotopy inverse. -/
def leftHomotopyMapLevelEquiv (H : Homotopy f f') (g : A ⟶ C) (n : ℕ) :
    ContinuousMap.HomotopyEquiv (Space f g n) (Space f' g n) where
  toFun := (leftHomotopyMap H g).map n
  invFun := (leftHomotopyMap H.symm g).map n
  left_inv := ⟨((leftHomotopyMapLeftHomotopy H g).levelHomotopy n).toHomotopy⟩
  right_inv := by
    have K := leftHomotopyMapLeftHomotopy H.symm g
    simp only [Homotopy.symm_symm] at K
    exact ⟨(K.levelHomotopy n).toHomotopy⟩

/-- The original pushout map changing only its right attaching arrow along a whole track. -/
def rightHomotopyMap (f : A ⟶ B) (H : Homotopy g g') :
    prespectrum f g ⟶ prespectrum f g' :=
  desc f g (inl f g') (inr f g') ((glue f g').trans (H.symm.postcomp (inr f g')))

/-- Right-arrow track composition retains its full left-associated cylinder parametrization. -/
theorem rightHomotopyMap_comp (f : A ⟶ B) (H : Homotopy g g') (K : Homotopy g' g'') :
    rightHomotopyMap f H ≫ rightHomotopyMap f K =
      desc f g (inl f g'') (inr f g'')
        (((glue f g'').trans (K.symm.postcomp (inr f g''))).trans
          (H.symm.postcomp (inr f g''))) := by
  apply hom_ext
  · apply Hom.ext; funext n; ext y; rfl
  · apply Hom.ext; funext n; ext z; rfl
  · intro n s x
    have he : (((glue f g').trans (H.symm.postcomp (inr f g'))).postcomp
        (rightHomotopyMap f K)) =
        ((glue f g'').trans (K.symm.postcomp (inr f g''))).trans
          (H.symm.postcomp (inr f g'')) := by
      rw [Homotopy.postcomp_trans]
      rw [show (glue f g').postcomp (rightHomotopyMap f K) =
        (glue f g'').trans (K.symm.postcomp (inr f g'')) from glue_desc _ _ _ _ _]
      congr 1
    exact congrArg (fun J ↦ J.level n (s, x)) he

/-- The actual doubled right-arrow track contracts with all original parameters retained. -/
def rightHomotopyMapCancelTrack (f : A ⟶ B) (H : Homotopy g g') :
    (((glue f g).trans (H.symm.symm.postcomp (inr f g))).trans
      (H.symm.postcomp (inr f g))).RelHomotopy (glue f g) := by
  let L := H.postcomp (inr f g)
  rw [Homotopy.symm_symm]
  rw [show H.symm.postcomp (inr f g) = L.symm from Homotopy.postcomp_symm H (inr f g)]
  exact (Homotopy.RelHomotopy.transAssoc (glue f g) L L.symm).trans
    (((Homotopy.RelHomotopy.refl (glue f g)).hcomp
      (Homotopy.RelHomotopy.reflTransSymm L).symm).trans
        (Homotopy.RelHomotopy.transRefl (glue f g)))

/-- Reversing the same right-arrow track is a genuine left inverse comparison. -/
def rightHomotopyMapLeftHomotopy (f : A ⟶ B) (H : Homotopy g g') :
    Homotopy (rightHomotopyMap f H ≫ rightHomotopyMap f H.symm) (𝟙 (prespectrum f g)) :=
  (descHomotopy f g (inl f g) (inr f g) (rightHomotopyMapCancelTrack f H)).cast
    (rightHomotopyMap_comp f H H.symm).symm (desc_self f g)

/-- The actual right-arrow change map has the constructed reverse-track homotopy inverse. -/
def rightHomotopyMapLevelEquiv (f : A ⟶ B) (H : Homotopy g g') (n : ℕ) :
    ContinuousMap.HomotopyEquiv (Space f g n) (Space f g' n) where
  toFun := (rightHomotopyMap f H).map n
  invFun := (rightHomotopyMap f H.symm).map n
  left_inv := ⟨((rightHomotopyMapLeftHomotopy f H).levelHomotopy n).toHomotopy⟩
  right_inv := by
    have K := rightHomotopyMapLeftHomotopy f H.symm
    simp only [Homotopy.symm_symm] at K
    exact ⟨(K.levelHomotopy n).toHomotopy⟩

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutArrowHomotopy.lean:1-150"
  "adaptation" "Actual whole-track descent and its original homotopy comparison"]
  leftHomotopyMapLevelEquiv

end Topology.LoopPrespectrum.HomotopyPushout

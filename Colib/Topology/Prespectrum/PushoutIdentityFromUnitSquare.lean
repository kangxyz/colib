/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.HomotopySquareBoundary
public import Colib.Topology.Prespectrum.HomotopySquareInterchange
public import Colib.Topology.Prespectrum.HomotopySquarePathPasting
public import Colib.Topology.Prespectrum.PushoutHomotopySquare
public import Colib.Topology.Prespectrum.PushoutMovingHomotopy
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam

/-! # Identity homotopy of the original identical-leg pushout

A whole unit square for the common leg gives a homotopy from the original moving-span map
to the literal identity. Its two charts retain the prescribed unit track; on the original
overlap cylinder it evaluates the constructed square at both independent parameters.
-/
/-! Implementation provenance: the identical-leg square of
`Quillen/Topology/Prespectrum/HomotopySquareComposition.lean:152-175` and
`Quillen/Topology/Prespectrum/PushoutIdentityFromUnitSquare.lean:24-85` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The constant track is the cone-independent
declaration from `Quillen/Topology/Prespectrum/ConeSquareMapMovingCoherence.lean:131-133`. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

/-- The literal identity leg square, changing only the endpoint arrows of the constant track. -/
def coneSquareIdentityTrack {A B : LoopPrespectrum.{u}} (f : A ⟶ B) :
    Homotopy (f ≫ 𝟙 B) ((𝟙 A) ≫ f) :=
  (Homotopy.refl f).cast (Category.comp_id f).symm (Category.id_comp f).symm

end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum.HomotopyPushout

/-- Two identical moving leg squares retain both charts and the actual moving middle cylinder. -/
def identicalLegMovingSquare {A B A' B' : LoopPrespectrum.{u}}
    (f : A ⟶ B) (f' : A' ⟶ B') {a₀ a₁ : A ⟶ A'} {b₀ b₁ : B ⟶ B'}
    (H₀ : Homotopy (f ≫ b₀) (a₀ ≫ f')) (H₁ : Homotopy (f ≫ b₁) (a₁ ≫ f'))
    (L : Homotopy a₀ a₁) (M : Homotopy b₀ b₁)
    (S : H₀.Square H₁ (Homotopy.precomp f M) (L.postcomp f')) :
    (mapSquareHomotopy f f f' f' a₀ b₀ b₀ H₀ H₀).Square
      (mapSquareHomotopy f f f' f' a₁ b₁ b₁ H₁ H₁)
      (Homotopy.precomp f (M.postcomp (inl f' f')))
      (Homotopy.precomp f (M.postcomp (inr f' f'))) := by
  let iL := inl f' f'
  let iR := inr f' f'
  let plus := (S.postcompose iL).ofBoundaryLevels
    (H₀.postcomp iL) (H₁.postcomp iL)
    (Homotopy.precomp f (M.postcomp iL))
    (L.postcomp (f' ≫ iL))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  let middle := Homotopy.Square.interchange L (glue f' f')
  let minus := (S.reversePaths.postcompose iR).ofBoundaryLevels
    (H₀.symm.postcomp iR) (H₁.symm.postcomp iR)
    (L.postcomp (f' ≫ iR))
    (Homotopy.precomp f (M.postcomp iR))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  exact plus.pastePaths (middle.pastePaths minus)

variable {A B : LoopPrespectrum.{u}} (f : A ⟶ B)

/-- The actual identity cylinder, with the target identities written as in map descent. -/
def identicalLegIdentityTargetTrack :
    Homotopy (f ≫ ((𝟙 B) ≫ inl f f)) (f ≫ ((𝟙 B) ≫ inr f f)) :=
  (glue f f).cast (by simp) (by simp)

/-- Both constant pieces of the identity square's original cylinder contract relatively. -/
def identicalLegIdentityTargetComparison :
    (mapSquareHomotopy f f f f (𝟙 A) (𝟙 B) (𝟙 B)
      (coneSquareIdentityTrack f) (coneSquareIdentityTrack f)).RelHomotopy
        (identicalLegIdentityTargetTrack f) := by
  have J := (Homotopy.RelHomotopy.reflTrans
    ((glue f f).trans (Homotopy.refl _))).trans (Homotopy.RelHomotopy.transRefl (glue f f))
  refine J.ofLevels _ _ ?_ (fun _ ↦ rfl)
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

variable {a : A ⟶ A} {b : B ⟶ B}
  (H : Homotopy (f ≫ b) (a ≫ f)) (L : Homotopy a (𝟙 A)) (M : Homotopy b (𝟙 B))
  (Q : H.Square (coneSquareIdentityTrack f) (Homotopy.precomp f M) (L.postcomp f))

/-- The complete overlap square has the exact chart units and the unpaused identity cylinder. -/
def identicalLegIdentityCylinderSquare :
    (mapSquareHomotopy f f f f a b b H H).Square (identicalLegIdentityTargetTrack f)
      (Homotopy.precomp f (M.postcomp (inl f f)))
      (Homotopy.precomp f (M.postcomp (inr f f))) :=
  ((identicalLegMovingSquare f f H (coneSquareIdentityTrack f) L M Q).toBoundary.trans
    (((Homotopy.RelHomotopy.refl (Homotopy.precomp f (M.postcomp (inl f f)))).hcomp
      (identicalLegIdentityTargetComparison f)).hcomp
        (Homotopy.RelHomotopy.refl (Homotopy.precomp f (M.postcomp (inr f f))).symm))).toSquare

/-- Descent of the actual identity cylinder and target charts is the literal identity. -/
theorem identicalLegIdentityTargetDesc :
    desc f f ((𝟙 B) ≫ inl f f) ((𝟙 B) ≫ inr f f)
      (identicalLegIdentityTargetTrack f) = 𝟙 (prespectrum f f) := by
  apply hom_ext
  · simp only [inl_desc, Category.id_comp, Category.comp_id]
  · simp only [inr_desc, Category.id_comp, Category.comp_id]
  · intro n s x
    rfl

/-- A genuine original unit square supplies a whole span identity with exact chart tracks. -/
def identicalLegIdentityHomotopy :
    Homotopy (mapOfHomotopies f f f f a b b H H) (𝟙 (prespectrum f f)) :=
  (descSquareHomotopy f f (M.postcomp (inl f f)) (M.postcomp (inr f f))
    (identicalLegIdentityCylinderSquare f H L M Q)).cast rfl (identicalLegIdentityTargetDesc f)

/-- The first complete chart is the specified original unit, without added constant time. -/
theorem identicalLegIdentityHomotopy_inl (n : ℕ) (r : unitInterval) (x : B.space n) :
    (identicalLegIdentityHomotopy f H L M Q).level n (r, (inl f f).map n x) =
      (inl f f).map n (M.level n (r, x)) := rfl

/-- The second complete chart is the same original unit, without added constant time. -/
theorem identicalLegIdentityHomotopy_inr (n : ℕ) (r : unitInterval) (x : B.space n) :
    (identicalLegIdentityHomotopy f H L M Q).level n (r, (inr f f).map n x) =
      (inr f f).map n (M.level n (r, x)) := rfl

/-- Every original cylinder point retains both independent parameters of the constructed square. -/
theorem identicalLegIdentityHomotopy_cylinder (n : ℕ) (r s : unitInterval) (x : A.space n) :
    (identicalLegIdentityHomotopy f H L M Q).level n (r, cylinder f f n (s, x)) =
      (identicalLegIdentityCylinderSquare f H L M Q).level n (r, (s, x)) := rfl

end Topology.LoopPrespectrum.HomotopyPushout

attribute [colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutIdentityFromUnitSquare.lean:65-85"
  "adaptation" "Original moving-span map to the literal identity, with chart and cylinder values"]
  Topology.LoopPrespectrum.HomotopyPushout.identicalLegIdentityHomotopy
  Topology.LoopPrespectrum.HomotopyPushout.identicalLegIdentityHomotopy_inl
  Topology.LoopPrespectrum.HomotopyPushout.identicalLegIdentityHomotopy_inr
  Topology.LoopPrespectrum.HomotopyPushout.identicalLegIdentityHomotopy_cylinder

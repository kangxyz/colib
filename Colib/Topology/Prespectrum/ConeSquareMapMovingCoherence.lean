/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Topology.Prespectrum.ConeSquareMapComposition
public import Colib.Topology.Prespectrum.HomotopySquareInterchange
public import Colib.Topology.Prespectrum.PushoutIdentityFromUnitSquare

/-!
# Cone Square Map Moving Coherence

Conditional whole cone coherence from moving original comparison squares.
The inclusion moves through the supplied track exactly, without a new constant time segment.

Adapted from Quillen's `Topology/Prespectrum/ConeSquareMapMovingCoherence.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The literal identity track
is reused from the native pushout unit module.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F) {g₀ g₁ : F ⟶ G}
  {H₀ : Homotopy (f ≫ g₀) (zeroHom E G)} {H₁ : Homotopy (f ≫ g₁) (zeroHom E G)}
  (L : Homotopy g₀ g₁)
  (S : H₀.Square H₁ (Homotopy.precomp f L) (Homotopy.refl (zeroHom E G)))

/-- Moving inclusion tracks and complete null squares descend together on the original cone. -/
def mappingConeDescSquareHomotopy :
    Homotopy (mappingConeDesc f g₀ H₀) (mappingConeDesc f g₁ H₁) :=
  mappingConeHomotopyOfNullSquare f
    (L.cast (mappingConeInclusion_desc f g₀ H₀).symm
      (mappingConeInclusion_desc f g₁ H₁).symm)
    (S.ofBoundaryLevels _ _ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun _ ↦ rfl))

/-- Descent retains every point of the prescribed inclusion track. -/
theorem mappingConeDescSquareHomotopy_inclusion (n : ℕ) (r : unitInterval) (x : F.space n) :
    (mappingConeDescSquareHomotopy f L S).level n (r, (mappingConeInclusion f).map n x) =
      L.level n (r, x) := rfl

/-- Descent retains the complete supplied square in its original two coordinates. -/
theorem mappingConeDescSquareHomotopy_cylinder (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (mappingConeDescSquareHomotopy f L S).level n
      (r, ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x)) =
        S.level n (r, (s, x)) := rfl

section Moving
variable {E' F' : LoopPrespectrum.{u}} (g : E' ⟶ F')
  {a₀ a₁ : E ⟶ E'} {b₀ b₁ : F ⟶ F'}
  (H : Homotopy (f ≫ b₀) (a₀ ≫ g)) (K : Homotopy (f ≫ b₁) (a₁ ≫ g))
  (A : Homotopy a₀ a₁) (B : Homotopy b₀ b₁)
  (Q : H.Square K (Homotopy.precomp f B) (A.postcomp g))

/-- The original comparison square and target null track supply a whole moving null square. -/
def coneSquareNullMovingSquare :
    (mappingConeSquareNullHomotopy f g a₀ b₀ H).Square
      (mappingConeSquareNullHomotopy f g a₁ b₁ K)
      (Homotopy.precomp f (B.postcomp (mappingConeInclusion g)))
      (Homotopy.refl (zeroHom E (mappingCone g))) := by
  let i := mappingConeInclusion g
  let first := (Q.postcompose i).ofBoundaryLevels
    (H.postcomp i) (K.postcomp i) (Homotopy.precomp f (B.postcomp i))
    (A.postcomp (g ≫ i))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  let last := (Homotopy.Square.interchange A (mappingConeHomotopy g)).ofBoundaryLevels
    (Homotopy.precomp a₀ (mappingConeHomotopy g))
    (Homotopy.precomp a₁ (mappingConeHomotopy g))
    (A.postcomp (g ≫ i)) (Homotopy.refl (zeroHom E (mappingCone g)))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  exact first.pastePaths last

end Moving

section Composition
variable {E' F' E'' F'' : LoopPrespectrum.{u}}
  (g : E' ⟶ F') (h : E'' ⟶ F'')
  (a : E ⟶ E') (b : F ⟶ F') (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))
  {e : E ⟶ E''} {l : F ⟶ F''} (T : Homotopy (f ≫ l) (e ≫ h))
  (A : Homotopy e (a ≫ c)) (B : Homotopy l (b ≫ d))
  (Q : T.Square (coneSquarePastedHomotopy f g h a b c d H K)
    (Homotopy.precomp f B) (A.postcomp h))

/-- The full geometric comparison square supplies the exact direct-to-composite null square.
The relative boundary conversion absorbs the cone reassociation while preserving `B` literally. -/
def coneSquareCompositionMovingNullSquare :
    (mappingConeSquareNullHomotopy f h e l T).Square
      (coneSquareCompositeNullHomotopy f g h a b c d H K)
      (Homotopy.precomp f (B.postcomp (mappingConeInclusion h)))
      (Homotopy.refl (zeroHom E (mappingCone h))) := by
  let J := coneSquareNullMovingSquare f h T
    (coneSquarePastedHomotopy f g h a b c d H K) A B Q
  let R := coneSquareCompositionNullComparison f g h a b c d H K
  exact (J.toBoundary.trans
    (((Homotopy.RelHomotopy.refl
      (Homotopy.precomp f (B.postcomp (mappingConeInclusion h)))).hcomp R).hcomp
      (Homotopy.RelHomotopy.refl (Homotopy.refl (zeroHom E (mappingCone h))).symm))).toSquare

/-- A proved original comparison square induces whole composition of the original cone maps.
This theorem does not assume or substitute a normalized cone map. -/
def coneSquareCompositionHomotopyOfSquare :
    Homotopy (mappingConeSquareMap f h e l T)
      (mappingConeSquareMap f g a b H ≫ mappingConeSquareMap g h c d K) :=
  (mappingConeDescSquareHomotopy f (B.postcomp (mappingConeInclusion h))
    (coneSquareCompositionMovingNullSquare f g h a b c d H K T A B Q)).cast rfl
      (coneSquareCompositeDesc f g h a b c d H K)

/-- The constructed whole law preserves every original Laurent composition point. -/
theorem coneSquareCompositionHomotopyOfSquare_inclusion
    (n : ℕ) (r : unitInterval) (x : F.space n) :
    (coneSquareCompositionHomotopyOfSquare f g h a b c d H K T A B Q).level n
      (r, (mappingConeInclusion f).map n x) =
        (mappingConeInclusion h).map n (B.level n (r, x)) := rfl

/-- The whole cone-cylinder law uses exactly its constructed two-parameter null square. -/
theorem coneSquareCompositionHomotopyOfSquare_cylinder
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (coneSquareCompositionHomotopyOfSquare f g h a b c d H K T A B Q).level n
      (r, ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x)) =
        (coneSquareCompositionMovingNullSquare f g h a b c d H K T A B Q).level n
          (r, (s, x)) := rfl

end Composition
section Identity
variable {a : E ⟶ E} {b : F ⟶ F}
  (T : Homotopy (f ≫ b) (a ≫ f)) (A : Homotopy a (𝟙 E)) (B : Homotopy b (𝟙 F))

/-- Even the constant-square cone map has an initial constant half to contract explicitly. -/
def coneSquareIdentityNullComparison :
    (mappingConeSquareNullHomotopy f f (𝟙 E) (𝟙 F) (coneSquareIdentityTrack f)).RelHomotopy
      (mappingConeHomotopy f) := by
  apply Homotopy.RelHomotopy.ofLevels (Homotopy.RelHomotopy.reflTrans (mappingConeHomotopy f))
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    rfl

variable (Q : T.Square (coneSquareIdentityTrack f)
  (Homotopy.precomp f B) (A.postcomp f))

/-- A complete original identity comparison square yields its complete original null square. -/
def coneSquareIdentityMovingNullSquare :
    (mappingConeSquareNullHomotopy f f a b T).Square (mappingConeHomotopy f)
      (Homotopy.precomp f (B.postcomp (mappingConeInclusion f)))
      (Homotopy.refl (zeroHom E (mappingCone f))) := by
  let J := coneSquareNullMovingSquare f f T (coneSquareIdentityTrack f) A B Q
  exact (J.toBoundary.trans
    (((Homotopy.RelHomotopy.refl
      (Homotopy.precomp f (B.postcomp (mappingConeInclusion f)))).hcomp
        (coneSquareIdentityNullComparison f)).hcomp
      (Homotopy.RelHomotopy.refl (Homotopy.refl (zeroHom E (mappingCone f))).symm))).toSquare

/-- The original whole cone identity follows from its actual unit comparison square. -/
def coneSquareIdentityHomotopyOfSquare :
    Homotopy (mappingConeSquareMap f f a b T) (𝟙 (mappingCone f)) :=
  (mappingConeDescSquareHomotopy f (B.postcomp (mappingConeInclusion f))
    (coneSquareIdentityMovingNullSquare f T A B Q)).cast rfl (mappingConeDesc_self f)

/-- The conditional whole identity retains the original unit track exactly. -/
theorem coneSquareIdentityHomotopyOfSquare_inclusion
    (n : ℕ) (r : unitInterval) (x : F.space n) :
    (coneSquareIdentityHomotopyOfSquare f T A B Q).level n
      (r, (mappingConeInclusion f).map n x) =
        (mappingConeInclusion f).map n (B.level n (r, x)) := rfl

/-- The conditional whole identity retains the complete constructed null square. -/
theorem coneSquareIdentityHomotopyOfSquare_cylinder
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (coneSquareIdentityHomotopyOfSquare f T A B Q).level n
      (r, ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x)) =
        (coneSquareIdentityMovingNullSquare f T A B Q).level n (r, (s, x)) := rfl

end Identity
end Topology.LoopPrespectrum

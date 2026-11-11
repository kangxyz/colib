/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.ConeTrackEquivariance
public import Colib.KTheory.Bass.LoopStrengthConeAction

/-! # Natural whole tracks for finite cone and loop recursion -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u v w
namespace KTheory.Bass.NaturalTrack
variable {C : Type u} [Category.{v} C] (L : C ⥤ C) (c : 𝟭 C ⟶ L)

/-- Only an original whole track and its ordinary same-time coefficient naturality. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:23-34"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
structure Track (F : C ⥤ LoopPrespectrum.{w}) where
  /-- The original self-track of the coefficient projection. -/
  homotopy (X : C) : Homotopy (F.map (c.app X)) (F.map (c.app X))
  /-- The independent original track time is preserved by coefficient arrows. -/
  naturality {X Y : C} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
      (x : (F.obj X).space n) :
    (F.map (L.map g)).map n ((homotopy X).level n (r, x)) =
      (homotopy Y).level n (r, (F.map g).map n x)

variable {L c} {F G K : C ⥤ LoopPrespectrum.{w}}

/-- Transport only along the specified equality of complete diagram functors. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:35-37"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
def Track.cast (A : Track L c F) (h : F = G) : Track L c G := h ▸ A

/-- Pointwise parameter looping of the same whole natural track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:38-48"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
def Track.loop (A : Track L c F) : Track L c (F ⋙ parameterLoopingFunctor) where
  homotopy X := (A.homotopy X).parameterLooping
  naturality := LoopConeTrack.loop_naturality L c F A.homotopy A.naturality

variable (Q : C ⥤ Arrow (Arrow C))
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- The original cone action, with its original inverse index map. -/
@[colib_tag "COL-0523", colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:49-53"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
def Track.cone (A : Track L c F) : Track L c (ConeTrack.diagram Q F) where
  homotopy := ConeTrack.action Q L c χ hχ F A.homotopy A.naturality
  naturality := ConeTrack.action_naturality Q L c χ hχ F A.homotopy A.naturality

/-- The actual Bass action is the pointwise loop of that original cone action. -/
@[colib_tag "COL-0523", colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:54-57"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
def Track.bass (A : Track L c F) : Track L c ((strictDiagramFunctor Q).obj F) :=
  (A.cone Q χ hχ).loop

/-- A local whole-time intertwining equation, rather than a tower coherence datum. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:58-61"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
def Equivariant (A : Track L c F) (B : Track L c G) (η : F ⟶ G) : Prop :=
  ∀ X r, η.app X ≫ (B.homotopy X).at r = (A.homotopy X).at r ≫ η.app (L.obj X)

/-- The unchanged identity intertwines every original track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:62-66"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem Equivariant.id (A : Track L c F) : Equivariant A A (𝟙 F) := by
  intro X r
  simp

/-- Composition preserves the same local whole-time equations. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:67-75"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem Equivariant.comp {A : Track L c F} {B : Track L c G} {D : Track L c K}
    {η : F ⟶ G} {θ : G ⟶ K} (hη : Equivariant A B η) (hθ : Equivariant B D θ) :
    Equivariant A D (η ≫ θ) := by
  intro X r
  change (η.app X ≫ θ.app X) ≫ (D.homotopy X).at r =
    (A.homotopy X).at r ≫ (η.app (L.obj X) ≫ θ.app (L.obj X))
  rw [Category.assoc, hθ, ← Category.assoc, hη, Category.assoc]

/-- The specified target equality transport retains the whole track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:76-81"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem Equivariant.cast_target (A : Track L c F) (h : F = G) :
    Equivariant A (A.cast h) (eqToHom h) := by
  subst G
  exact Equivariant.id A

/-- The specified source equality transport retains the whole track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:82-87"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem Equivariant.cast_source (B : Track L c G) (h : F = G) :
    Equivariant (B.cast h.symm) B (eqToHom h) := by
  subst G
  exact Equivariant.id B

/-- Original cone maps preserve actual local whole-track intertwiners. -/
@[colib_tag "COL-0523", colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:88-94"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem Equivariant.cone {A : Track L c F} {B : Track L c G} {η : F ⟶ G}
    (hη : Equivariant A B η) :
    Equivariant (A.cone Q χ hχ) (B.cone Q χ hχ) (ConeTrack.map Q η) :=
  ConeTrackEquivariance.cone_action Q L c χ hχ
    A.homotopy B.homotopy A.naturality B.naturality η hη

/-- Original loop maps preserve the same local whole-track intertwiners. -/
@[colib_tag "COL-0523", colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:95-100"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem Equivariant.loop {A : Track L c F} {B : Track L c G} {η : F ⟶ G}
    (hη : Equivariant A B η) :
    Equivariant A.loop B.loop (Functor.whiskerRight η parameterLoopingFunctor) :=
  ConeTrackEquivariance.loop_action L c A.homotopy B.homotopy η hη

/-- The original Bass map preserves the original induced Bass action. -/
@[colib_tag "COL-0523", colib_ref "quillen"
  "Quillen/KTheory/Bass/NaturalTrack.lean:101-105"
  "adaptation" "Original whole-track transport, explicit inverse index map and unchanged time"]
theorem Equivariant.bass {A : Track L c F} {B : Track L c G} {η : F ⟶ G}
    (hη : Equivariant A B η) :
    Equivariant (A.bass Q χ hχ) (B.bass Q χ hχ) ((strictDiagramFunctor Q).map η) :=
  (hη.cone Q χ hχ).loop

end KTheory.Bass.NaturalTrack

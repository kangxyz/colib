/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.RetainedGeometry

/-! # The same full boundary through base change and component restriction

Both boundaries are literal scheme pullbacks. Their complement equality and finiteness are
preserved without reducing their scheme structure or inferring nonemptiness from finiteness.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme

/-- The full boundary is still the complement of the same twice-retained open. -/
theorem range_baseComponent_fullBoundary
    {X Xnew Y D : Scheme.{u}} [IsLocallyNoetherian Xnew] [IsNormal Xnew]
    (F : Xnew ⟶ X) (j : Y ⟶ X) (d : D ⟶ X)
    (hd : Set.range d = (Set.range j)ᶜ) (x : Xnew) :
    Set.range (pullback.fst (normalComponentOpen x).ι (pullback.fst F d)) =
      (Set.range (pullback.fst (normalComponentOpen x).ι (pullback.fst F j)))ᶜ := by
  apply range_normalComponentBoundary
  rw [Pullback.range_fst, Pullback.range_fst, hd]
  rfl

/-- Finiteness of the original full boundary over the base survives the actual base change. -/
instance isFinite_baseChanged_fullBoundary
    {X A Anew D : Scheme.{u}} (q : X ⟶ A) (g : Anew ⟶ A) (d : D ⟶ X)
    [IsFinite (d ≫ q)] :
    IsFinite (pullback.fst (pullback.fst q g) d ≫ pullback.snd q g) := by
  exact MorphismProperty.of_isPullback (P := @IsFinite)
    ((IsPullback.of_hasPullback (pullback.fst q g) d).flip.paste_vert
      (IsPullback.of_hasPullback q g)) inferInstance

/-- Restrict that literal boundary to the same marked component, preserving finiteness. -/
instance isFinite_baseComponent_fullBoundary
    {X A Anew D : Scheme.{u}} (q : X ⟶ A) (g : Anew ⟶ A) (d : D ⟶ X)
    [IsLocallyNoetherian (pullback q g)] [IsNormal (pullback q g)]
    [IsFinite (d ≫ q)] (x : (pullback q g : Scheme.{u})) :
    IsFinite (pullback.fst (normalComponentOpen (X := pullback q g) x).ι
      (pullback.fst (pullback.fst q g) d) ≫
      (normalComponentOpen (X := pullback q g) x).ι ≫ pullback.snd q g) := by
  infer_instance

end AlgebraicGeometry.Scheme

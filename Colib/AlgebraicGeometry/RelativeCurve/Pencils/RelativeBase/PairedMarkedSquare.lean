/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-! # The paired marked square in the projective compactification -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

/-- The whole original marked square is unchanged inside the target
projective compactification. -/
theorem pairedMark_isPullback {X Y P C Z : Scheme.{u}}
    (f : C ⟶ P) (j : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
    (z : Z ⟶ X) (s : Z ⟶ Y) [Mono jA] (H : IsPullback s (𝟙 Z) p z) :
    IsPullback s (𝟙 Z) (j ≫ f) (z ≫ jA) := by
  rw [hRet]
  have h : IsPullback z (𝟙 Z) jA (z ≫ jA) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa only [Category.id_comp] using H.paste_vert h

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

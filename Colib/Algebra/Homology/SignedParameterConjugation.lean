/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs

/-! # External endpoint conjugation of the native signed parameter arrow

Reconstructed from the native signed-transport formula and the recovered joint-pair
consumer. The original parameter morphism and additive-shift boundary are retained.
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Functor

variable {C : Type*} [Category C] [HasShift C ℤ]
variable (G : C ⥤ C) [G.CommShift ℤ]

/-- Place the original parameter morphism using its native shift comparisons. -/
def signedParameterArrow {M N X Y : C} (g : M ⟶ G.obj N)
    (t s : ℤ) (hs : t + 1 = s)
    (a : X ≅ (shiftFunctor C s).obj M) (b : Y ≅ (shiftFunctor C t).obj N) :
    X ⟶ G.obj ((shiftFunctor C (1 : ℤ)).obj Y) :=
  a.hom ≫ (shiftFunctor C s).map g ≫ (G.commShiftIso s).inv.app N ≫
    G.map ((shiftFunctorAdd' C t 1 s hs).hom.app N ≫
      (shiftFunctor C (1 : ℤ)).map b.inv)

/-- Cancel only the external endpoint isomorphisms, preserving the native shift boundary. -/
theorem signedParameterArrow_conjugate {M N X Y X₀ Y₀ : C} (g : M ⟶ G.obj N)
    (t s : ℤ) (hs : t + 1 = s)
    (a : X ≅ (shiftFunctor C s).obj M) (b : Y ≅ (shiftFunctor C t).obj N)
    (c : X₀ ≅ X) (d : Y₀ ≅ Y) :
    c.inv ≫ signedParameterArrow G g t s hs (c ≪≫ a) (d ≪≫ b) ≫
      G.map ((shiftFunctor C (1 : ℤ)).map d.hom) =
    signedParameterArrow G g t s hs a b := by
  simp [signedParameterArrow, Category.assoc, ← Functor.map_comp]

/-- With identity endpoint isomorphisms, only the native signed comparison remains. -/
theorem signedParameterArrow_refl {M N : C} (g : M ⟶ G.obj N)
    (t s : ℤ) (hs : t + 1 = s) :
    signedParameterArrow G g t s hs (Iso.refl _) (Iso.refl _) =
      (shiftFunctor C s).map g ≫ (G.commShiftIso s).inv.app N ≫
        G.map ((shiftFunctorAdd' C t 1 s hs).hom.app N) := by
  simp [signedParameterArrow]

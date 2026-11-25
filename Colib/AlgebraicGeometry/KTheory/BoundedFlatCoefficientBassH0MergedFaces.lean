/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0MergedNodes

/-!
# The thirteen native faces of the common Bass 62-simplex

The three primitive faces of each of the four charts, together with the
entire bottom product simplex, are actual faces in the retained order.
Only these geometric face restrictions are asserted; no scalar gluing
or comparison is used. Adapted from `BassSupportOrder.lean` and
`BassH0MergedFaces.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`
in Quillen.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged

/-- The three original full split-triple faces of a coefficient rectangle. -/
def rectangleFace (i : Fin 3) : ⦋7⦌ ⟶ ⦋17⦌ :=
  ![BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace,
    BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace,
    BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace] i

/-- Each of these three original whole seven-faces retains its native order. -/
theorem oldPlus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘
      (rectangleFace i ≫ (BoundedFlatCoefficientBassOverlap.plusFace ≫
        BoundedFlatCoefficientBassReferenceMerge.chartFace)).toOrderHom) := by
  fin_cases i <;> decide

/-- The `i`th original positive-chart 7-face reindexed into the 63 scalar slots. -/
def oldPlusFace (i : Fin 3) : ⦋7⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨oldIndex ∘ (rectangleFace i ≫
    (BoundedFlatCoefficientBassOverlap.plusFace ≫
      BoundedFlatCoefficientBassReferenceMerge.chartFace)).toOrderHom,
    oldPlus_monotone i⟩

/-- Each of these three original whole seven-faces retains its native order. -/
theorem oldMinus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘
      (rectangleFace i ≫ (BoundedFlatCoefficientBassOverlap.minusFace ≫
        BoundedFlatCoefficientBassReferenceMerge.chartFace)).toOrderHom) := by
  fin_cases i <;> decide

/-- The `i`th original inverse-coordinate-chart 7-face reindexed into the 63 scalar slots. -/
def oldMinusFace (i : Fin 3) : ⦋7⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨oldIndex ∘ (rectangleFace i ≫
    (BoundedFlatCoefficientBassOverlap.minusFace ≫
      BoundedFlatCoefficientBassReferenceMerge.chartFace)).toOrderHom,
    oldMinus_monotone i⟩

/-- Each of these three original whole seven-faces retains its native order. -/
theorem h0Plus_monotone (i : Fin 3) :
    Monotone (h0Index ∘
      (rectangleFace i ≫ (BoundedFlatCoefficientBassH0Diagram.plusFace)).toOrderHom) := by
  fin_cases i <;> decide

/-- The `i`th H0 positive-chart 7-face reindexed into the 63 scalar slots. -/
def h0PlusFace (i : Fin 3) : ⦋7⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨h0Index ∘ (rectangleFace i ≫
    (BoundedFlatCoefficientBassH0Diagram.plusFace)).toOrderHom, h0Plus_monotone i⟩

/-- Each of these three original whole seven-faces retains its native order. -/
theorem h0Minus_monotone (i : Fin 3) :
    Monotone (h0Index ∘
      (rectangleFace i ≫ (BoundedFlatCoefficientBassH0Diagram.minusFace)).toOrderHom) := by
  fin_cases i <;> decide

/-- The `i`th H0 inverse-coordinate-chart 7-face reindexed into the 63 scalar slots. -/
def h0MinusFace (i : Fin 3) : ⦋7⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨h0Index ∘ (rectangleFace i ≫
    (BoundedFlatCoefficientBassH0Diagram.minusFace)).toOrderHom, h0Minus_monotone i⟩

/-- The complete original bottom fourteen-simplex also retains its order. -/
theorem bottom_monotone :
    Monotone (oldIndex ∘ BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom) := by
  decide

/-- The complete bottom 14-face reindexed into the 63 scalar slots with its original order. -/
def supportedBottomFace : ⦋14⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨oldIndex ∘
    BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom, bottom_monotone⟩

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

theorem oldPlus_face (i : Fin 3) :
    (simplex P u v).face (oldPlusFace i) =
      (BoundedFlatCoefficientBassReferenceMerge.simplex P u v).face
        (rectangleFace i ≫
          (BoundedFlatCoefficientBassOverlap.plusFace ≫
            BoundedFlatCoefficientBassReferenceMerge.chartFace)) :=
  old_face P u v _ (oldPlus_monotone i)

theorem oldMinus_face (i : Fin 3) :
    (simplex P u v).face (oldMinusFace i) =
      (BoundedFlatCoefficientBassReferenceMerge.simplex P u v).face
        (rectangleFace i ≫
          (BoundedFlatCoefficientBassOverlap.minusFace ≫
            BoundedFlatCoefficientBassReferenceMerge.chartFace)) :=
  old_face P u v _ (oldMinus_monotone i)

theorem h0Plus_face (i : Fin 3) :
    (simplex P u v).face (h0PlusFace i) =
      (BoundedFlatCoefficientBassH0Merge.simplex P u v).face
        (rectangleFace i ≫ BoundedFlatCoefficientBassH0Diagram.plusFace) :=
  h0_face P u v _ (h0Plus_monotone i)

theorem h0Minus_face (i : Fin 3) :
    (simplex P u v).face (h0MinusFace i) =
      (BoundedFlatCoefficientBassH0Merge.simplex P u v).face
        (rectangleFace i ≫ BoundedFlatCoefficientBassH0Diagram.minusFace) :=
  h0_face P u v _ (h0Minus_monotone i)

/-- The entire original bottom product simplex is retained as an actual full fourteen-face. -/
theorem bottom_face : (simplex P u v).face supportedBottomFace =
    BoundedFlatCoefficientBassLaurentBottomFace.simplex P u v :=
  (old_face P u v BoundedFlatCoefficientBassReferenceMerge.bottomFace bottom_monotone).trans
    (BoundedFlatCoefficientBassReferenceMerge.bottom_face P u v)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged

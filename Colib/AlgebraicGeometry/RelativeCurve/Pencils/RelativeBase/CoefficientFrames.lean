/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.FullBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.SourceChangedCoordinateUnit
/-! # Pull the constructed full relative boundary frames to both source products -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S C Y D Z X A : Scheme.{u}}
  (π : C ⟶ S) (j : Y ⟶ C) (s : Z ⟶ Y) (d : D ⟶ C)
  (L : C.Modules)
  (eD : (Modules.pullback d).obj L ≅ SheafOfModules.unit D.ringCatSheaf)
  (eZ : (Modules.pullback (s ≫ j)).obj L ≅ SheafOfModules.unit Z.ringCatSheaf)

include eD eZ in
/-- A coefficient frame on the original whole lambda boundary, pulled from
the two whole finite-boundary frames produced on the common base. -/
theorem lambdaCoefficientFrame :
    Nonempty ((Modules.pullback (fullGraphBoundaryMap π j s d)).obj
      ((Modules.pullback (pullback.snd (j ≫ π) π)).obj L) ≅
        SheafOfModules.unit
          ((pullback (pullback.snd (j ≫ π) π) d) ⨿
            pullback (j ≫ π) (s ≫ j ≫ π)).ringCatSheaf) := by
  let eI := sourceChangedBoundaryFrame (pullback.snd (j ≫ π) π) d
    (infinityProductMap π j d) (pullback.snd _ _) (pullback.condition) L eD
  let eS := sourceChangedBoundaryFrame (pullback.snd (j ≫ π) π) (s ≫ j)
    (markedProductMap π j s) (pullback.snd _ _) (by simp [markedProductMap]) L eZ
  obtain ⟨E, -, -⟩ := exists_boundaryCoprod_frame (infinityProductMap π j d)
    (markedProductMap π j s) ((Modules.pullback (pullback.snd (j ≫ π) π)).obj L) eI eS
  exact ⟨E⟩

variable (q : X ⟶ S) (p : Y ⟶ X) (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) (z : Z ⟶ X) (hs : s ≫ p = z)

include eD eZ in
/-- The independent whole psi boundary has its own coefficient frame on the
complete correction source of the refined diagram. -/
theorem psiCoefficientFrame :
    Nonempty ((Modules.pullback (psiBoundaryInclusion q π j p hq a z s hs d)).obj
      ((Modules.pullback (pullback.snd (a ≫ q) π)).obj L) ≅
        SheafOfModules.unit
          ((pullback (pullback.snd (a ≫ q) π) d) ⨿ pullback (a ≫ q) (z ≫ q)).ringCatSheaf) := by
  let eI := sourceChangedBoundaryFrame (pullback.snd (a ≫ q) π) d
    (pullback.fst (pullback.snd (a ≫ q) π) d) (pullback.snd _ _) pullback.condition L eD
  let eS := sourceChangedBoundaryFrame (pullback.snd (a ≫ q) π) (s ≫ j)
    (psiZeroInclusion q π j p hq a z s hs) (pullback.snd _ _)
    (by simp [psiZeroInclusion]) L eZ
  obtain ⟨E, -, -⟩ := exists_boundaryCoprod_frame (pullback.fst (pullback.snd (a ≫ q) π) d)
    (psiZeroInclusion q π j p hq a z s hs)
    ((Modules.pullback (pullback.snd (a ≫ q) π)).obj L) eI eS
  exact ⟨E⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

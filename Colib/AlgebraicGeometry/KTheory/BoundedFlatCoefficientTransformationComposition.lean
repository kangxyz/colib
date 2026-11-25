/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientCompositionTracks
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquareTrackOriginal
public import Colib.Topology.Prespectrum.HomotopySquareBoundary
public import Colib.Topology.Prespectrum.HomotopySquareComposition

/-!
# Composition of exact coefficient transformation squares

A fixed natural transformation on coefficient algebras gives the actual geometric rectangle.
The two endpoints retain both complete composition tracks and the original association casts.
Adapted from `BoundedFlat/CoefficientTransformationComposition.lean` and the geometric square
lemmas in `BoundedFlat/CoefficientBassCoherence.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Reversing the geometric square swaps its two original composition routes. -/
theorem boundedAboveFlatGeometricSquareReverse_level {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
    (h : p ≫ v = q ≫ w) (n : ℕ) :
    (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy q w p v h.symm).symm.level n =
      (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p v q w h).level n := by
  exact Homotopy.reverseTwoRoutes_level
    (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy p v)
    (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q w)
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap h) n

/-- Equal geometric arrows identify full original square levels, independently of proof
    transport. -/
theorem boundedAboveFlatGeometricSquare_level_congr {X Y Z T : Scheme.{u}}
    {p p' : X ⟶ Y} {v v' : Y ⟶ Z} {q q' : X ⟶ T} {w w' : T ⟶ Z}
    (h : p ≫ v = q ≫ w) (h' : p' ≫ v' = q' ≫ w')
    (hp : p = p') (hv : v = v') (hq : q = q') (hw : w = w') (n : ℕ) :
    (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p v q w h).level n =
      (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p' v' q' w' h').level n := by
  subst p' v' q' w'
  rfl

namespace BoundedFlatCoefficientTransformationComposition

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {M N : Under R ⥤ Under R} (α : M ⟶ N)
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

local notation "K(" f ")" => boundedAboveFlatPerfectPullbackPrespectrumMap f

/-- The geometric equality is obtained by applying the actual coefficient construction. -/
theorem coefficientMapNaturality (u : a ⟶ b) :
    coefficientMap P (N.map u) ≫ coefficientMap P (α.app a) =
      coefficientMap P (α.app b) ≫ coefficientMap P (M.map u) := by
  rw [← coefficientMap_comp, ← coefficientMap_comp]
  exact congrArg (coefficientMap P) (α.naturality u).symm

/-- The actual functor-applied coefficient composition track. -/
def coefficientComposition (M : Under R ⥤ Under R) :=
  (boundedAboveFlatCoefficientCompositionHomotopy P (M.map u) (M.map v)).cast
    (congrArg (fun k ↦ boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P k))
      (M.map_comp u v)).symm rfl

/-- The original coefficient naturality square for the fixed transformation. -/
def square (u : a ⟶ b) :=
  boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy (coefficientMap P (N.map u))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (M.map u))
    (coefficientMapNaturality P α u)

/-- The actual original rectangle, in the coefficient-composition direction. -/
def rectangle :=
  BoundedFlatPerfectDoubleSquareTrack.originalComparison
    (coefficientMap P (M.map u)) (coefficientMap P (M.map v))
    (coefficientMap P (N.map u)) (coefficientMap P (N.map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientMapNaturality P α u).symm
    (coefficientMapNaturality P α v).symm

/-- Two successive ORIGINAL transformation squares, with literal associations. -/
def compositeSquare :=
  ((square P α u).postcomp (K(coefficientMap P (N.map v)))).trans
    ((Homotopy.precomp (K(coefficientMap P (M.map u)))
      (square P α v)).cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)

/-- The original source coefficient composition followed by the original chart map. -/
def sourceComposition :=
  (coefficientComposition P u v M).postcomp (boundedAboveFlatPerfectPullbackPrespectrumMap
    (coefficientMap P (α.app c)))

/-- The original target coefficient composition under the original source chart map. -/
def targetComposition :=
  (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P (α.app a)))
    (coefficientComposition P u v N)).cast rfl (Category.assoc _ _ _).symm

/-- The rectangle starts at the two complete reversed original transformation tracks. -/
theorem rectangle_source_level (n : ℕ) :
    (compositeSquare P α u v).level n =
      (((rectangle P α u v).symmPath).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  unfold BoundedFlatPerfectDoubleSquareTrack.originalLeft
  rw [Homotopy.symm_trans]
  apply Homotopy.trans_level_congr
  · rw [← Homotopy.postcomp_symm]
    apply Homotopy.postcomp_level_congr
    exact (boundedAboveFlatGeometricSquareReverse_level
      (coefficientMap P (N.map u)) (coefficientMap P (α.app a))
      (coefficientMap P (α.app b)) (coefficientMap P (M.map u))
      (coefficientMapNaturality P α u) n).symm
  · change (Homotopy.precomp (K(coefficientMap P (M.map u)))
      (square P α v)).level n =
        (Homotopy.precomp (K(coefficientMap P (M.map u)))
          (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy
            (coefficientMap P (α.app c)) (coefficientMap P (M.map v))
            (coefficientMap P (N.map v)) (coefficientMap P (α.app b))
            (coefficientMapNaturality P α
              v).symm)).symm.level n
    rw [← Homotopy.precomp_symm]
    apply Homotopy.precomp_level_congr
    exact (boundedAboveFlatGeometricSquareReverse_level
      (coefficientMap P (N.map v)) (coefficientMap P (α.app b))
      (coefficientMap P (α.app c)) (coefficientMap P (M.map v))
      (coefficientMapNaturality P α v) n).symm

/-- The whole target is the direct original square and both actual coefficient compositions. -/
theorem rectangle_target_level (n : ℕ) :
    (((targetComposition P α u v).symm.trans (square P α (u ≫ v))).trans
      (sourceComposition P α u v)).level n =
      (((rectangle P α u v).symmPath).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  unfold BoundedFlatPerfectDoubleSquareTrack.originalRight
  rw [Homotopy.symm_trans, Homotopy.symm_trans, Homotopy.symm_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · apply Homotopy.symm_level_congr
      rfl
    · refine (boundedAboveFlatGeometricSquareReverse_level
        (coefficientMap P (N.map (u ≫ v))) (coefficientMap P (α.app a))
        (coefficientMap P (α.app c)) (coefficientMap P (M.map (u ≫ v)))
        (coefficientMapNaturality P α (u ≫ v))
          n).symm.trans ?_
      apply Homotopy.symm_level_congr
      exact boundedAboveFlatGeometricSquare_level_congr _ _ rfl
        ((congrArg (coefficientMap P) (M.map_comp u v)).trans
          (coefficientMap_comp P (M.map u) (M.map v)))
        ((congrArg (coefficientMap P) (N.map_comp u v)).trans
          (coefficientMap_comp P (N.map u) (N.map v))) rfl n
  · rfl

/-- Original coefficient-square composition is constructed from the actual rectangle. -/
def comparison :
    (compositeSquare P α u v).RelHomotopy
      (((targetComposition P α u v).symm.trans (square P α (u ≫ v))).trans
        (sourceComposition P α u v)) :=
  Homotopy.RelHomotopy.ofLevels (rectangle P α u v).symmPath _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using rectangle_source_level P α u v n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using rectangle_target_level P α u v n)

/-- Rotate the actual original rectangle to the literal moving-square boundary. -/
def boundary :
    (square P α (u ≫ v)).RelHomotopy
      (((targetComposition P α u v).trans (compositeSquare P α u v)).trans
        (sourceComposition P α u v).symm) := by
  let B := targetComposition P α u v
  let A := sourceComposition P α u v
  let H := square P α (u ≫ v)
  let K := compositeSquare P α u v
  have J := comparison P α u v
  have route : (B.trans K).RelHomotopy (H.trans A) :=
    ((Homotopy.RelHomotopy.refl B).hcomp J).trans
      (((Homotopy.RelHomotopy.transAssoc B (B.symm.trans H) A).symm).trans
        ((((Homotopy.RelHomotopy.transAssoc B B.symm H).symm).hcomp
          (Homotopy.RelHomotopy.refl A)).trans
          ((((Homotopy.RelHomotopy.reflTransSymm B).symm.hcomp
            (Homotopy.RelHomotopy.refl H)).hcomp (Homotopy.RelHomotopy.refl A)).trans
            ((Homotopy.RelHomotopy.reflTrans H).hcomp (Homotopy.RelHomotopy.refl A)))))
  exact (Homotopy.RelHomotopy.transRefl H).symm.trans
    (((Homotopy.RelHomotopy.refl H).hcomp (Homotopy.RelHomotopy.reflTransSymm A)).trans
      (((Homotopy.RelHomotopy.transAssoc H A A.symm).symm).trans
        (route.symm.hcomp (Homotopy.RelHomotopy.refl A.symm))))

/-- Actual composition of the whole original transformation squares with original side tracks. -/
def movingSquare := (boundary P α u v).toSquare

end BoundedFlatCoefficientTransformationComposition
end AlgebraicGeometry.Scheme.Modules

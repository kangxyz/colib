/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputMap
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# The whole original global raw source-null input comparison

The unchanged positive-chart source-null compares across the actual scheme-arrow cone map.
The proof uses the original positive geometric pasting and independent source-leg/cone
interchange; no missing null compatibility is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

namespace InputNull

/-- The original positive-leg track after Laurent scheme-arrow change and cone inclusion. -/
def oldPositive :=
  ((plusHomotopy Y).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))).postcomp
      (mappingConeInclusion (comparison X))

/-- The actual positive scheme-arrow square on the original polynomial projection. -/
def positiveMovement :=
  ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
    (plusSquareHomotopy g)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).postcomp
        (mappingConeInclusion (comparison X))

/-- The original polynomial scheme-arrow track followed by the target positive Laurent leg. -/
def polynomialMovement :=
  ((polynomialSquareHomotopy g).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X))).postcomp
      (mappingConeInclusion (comparison X))

/-- The original common Laurent scheme-arrow square after target cone inclusion. -/
def laurentMovement :=
  (laurentSquareHomotopy g).postcomp
    (mappingConeInclusion (comparison X))

/-- The target positive-leg comparison preceded by the original base scheme-arrow map. -/
def newPositive :=
  ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    (plusHomotopy X)).cast rfl (Category.assoc _ _ _).symm).postcomp
      (mappingConeInclusion (comparison X))

/-- The previously proved geometric positive-chart pasting retains its full cone-image track. -/
def positivePasting :
    ((positiveMovement g).trans (polynomialMovement g)).RelHomotopy
      ((oldPositive g).symm.trans ((laurentMovement g).trans (newPositive g))) := by
  simpa only [plusInputLeftTrack, plusInputRightTrack,
    Homotopy.postcomp_trans, Homotopy.postcomp_symm, positiveMovement, polynomialMovement,
    oldPositive, laurentMovement, newPositive] using
    (plusInputPasting g).postcomp
      (mappingConeInclusion (comparison X))

/-- Cancel the actual positive-leg inverse to recover the genuine three-track geometric route. -/
def straightPositivePasting :
    (((oldPositive g).trans (positiveMovement g)).trans
      (polynomialMovement g)).RelHomotopy
        ((laurentMovement g).trans (newPositive g)) := by
  let A := oldPositive g
  let B := positiveMovement g
  let Q := polynomialMovement g
  let T := (laurentMovement g).trans (newPositive g)
  exact (Homotopy.RelHomotopy.transAssoc A B Q).trans
    (((Homotopy.RelHomotopy.refl A).hcomp (positivePasting g)).trans
      ((Homotopy.RelHomotopy.transAssoc A A.symm T).symm.trans
        (((Homotopy.RelHomotopy.reflTransSymm A).symm.hcomp
          (Homotopy.RelHomotopy.refl T)).trans (Homotopy.RelHomotopy.reflTrans T))))

/-- The old source-leg image traverses the original target cone cylinder. -/
def oldCone : Homotopy
    (((boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g)) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)) ≫
      mappingConeInclusion (comparison X)) (zeroHom _ _) :=
  (Homotopy.precomp (sourceLeg Y ≫
    spanMap g)
    (mappingConeHomotopy (comparison X))).cast (by
      apply Topology.LoopPrespectrum.Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      rfl) rfl

/-- The new source-leg image traverses the same original target cone cylinder. -/
def newCone : Homotopy
    (((boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)) ≫
      mappingConeInclusion (comparison X)) (zeroHom _ _) :=
  (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
    sourceLeg X)
    (mappingConeHomotopy (comparison X))).cast (by
      apply Topology.LoopPrespectrum.Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      rfl) rfl

/-- The original source-leg cone square supplies its actual polynomial-movement pasting. -/
def conePasting :
    (oldCone g).RelHomotopy ((polynomialMovement g).trans (newCone g)) := by
  let Z := Topology.LoopPrespectrum.Homotopy.refl (zeroHom
    (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace))
    (mappingCone (comparison X)))
  have J : (oldCone g).RelHomotopy
      (((polynomialMovement g).trans (newCone g)).trans Z) := by
    refine (sourceLegInputConeBoundary g).ofLevels _ _ ?_ ?_
    · intro n
      rfl
    · intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr
        · apply ContinuousMap.ext
          rintro ⟨s, x⟩
          rfl
        · rfl
      · rfl
  exact J.trans (Homotopy.RelHomotopy.transRefl _)

/-- The original positive geometry and actual cone square paste to the target null route. -/
def pastedNullComparison :
    ((oldPositive g).trans ((positiveMovement g).trans (oldCone g))).RelHomotopy
      ((laurentMovement g).trans ((newPositive g).trans (newCone g))) := by
  let A := oldPositive g
  let B := positiveMovement g
  let Q := polynomialMovement g
  let E := oldCone g
  let G := newCone g
  let L := laurentMovement g
  let F := newPositive g
  exact (Homotopy.RelHomotopy.transAssoc A B E).symm.trans
    (((Homotopy.RelHomotopy.refl (A.trans B)).hcomp (conePasting g)).trans
      ((Homotopy.RelHomotopy.transAssoc (A.trans B) Q G).symm.trans
        (((straightPositivePasting g).hcomp (Homotopy.RelHomotopy.refl G)).trans
          (Homotopy.RelHomotopy.transAssoc L F G))))

/-- The original old-fiber Laurent nullhomotopy followed by the actual scheme-arrow cone map. -/
def originalOldNull : Homotopy
    ((boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection.app Y) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g)) ≫
      mappingConeInclusion (comparison X)) (zeroHom _ _) :=
  ((sourceNull Y).postcomp
    (coneMap g)).cast (by
    apply Topology.LoopPrespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl) (by
      apply Topology.LoopPrespectrum.Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      exact (coneMap g).map_point n)

/-- The original target-fiber Laurent nullhomotopy preceded by actual base scheme-arrow change. -/
def originalNewNull : Homotopy
    ((boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection.app X)) ≫
      mappingConeInclusion (comparison X)) (zeroHom _ _) :=
  (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    (sourceNull X)).cast (Category.assoc _ _ _).symm rfl

/-- Every original target-null coordinate is its unchanged positive leg and cone cylinder. -/
lemma originalNewNull_level (n : ℕ) :
    (originalNewNull g).level n = ((newPositive g).trans (newCone g)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level]
  change ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    ((plusHomotopy X).postcomp
      (mappingConeInclusion (comparison X)))).trans
      (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
        (Homotopy.precomp (sourceLeg X)
          (mappingConeHomotopy (comparison X))))).level n = _
  apply Homotopy.trans_level_congr <;> rfl

/-- Each mapped old-null coordinate retains the positive leg and actual cone-square map. -/
lemma originalOldNull_level (n : ℕ) :
    (originalOldNull g).level n =
      ((oldPositive g).trans ((positiveMovement g).trans (oldCone g))).level n := by
  simp only [originalOldNull, Homotopy.cast_level, sourceNull, Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    rfl
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    rfl

/-- The two unchanged Laurent nullhomotopies compare along the actual Laurent scheme-arrow track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassInputNull.lean:209-216"
  "adaptation" "Original prescribed full source-null comparison after scheme pullback"]
def originalNullComparison :
    (originalOldNull g).RelHomotopy ((laurentMovement g).trans (originalNewNull g)) := by
  refine (pastedNullComparison g).ofLevels _ _ (originalOldNull_level g) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level g n

end InputNull

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass

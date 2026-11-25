/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityPositiveSupport
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputNull
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering
public import Colib.Topology.Prespectrum.RelativeHomotopyPostcompReparam

/-! The unchanged original positive-null pasting is performed in the actual positive cones.
The same geometric pasting, polynomial/cone interchange, associators and cancellations retain
every original comparison and null coordinate. Exact image comparison with the chosen full-cone
recipe is a separate theorem; no mixed higher filler is supplied here. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityPositiveNull
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original positive-leg track after Laurent scheme-arrow change and cone inclusion. -/
def oldPositive :=
  ((plusHomotopy Y).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))).postcomp
      (mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))

/-- The actual positive scheme-arrow square on the original polynomial projection. -/
def positiveMovement :=
  ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
    (plusSquareHomotopy g)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).postcomp
        (mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))

/-- The original polynomial scheme-arrow track followed by the target positive Laurent leg. -/
def polynomialMovement :=
  ((polynomialSquareHomotopy g).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X))).postcomp
      (mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))

/-- The original common Laurent scheme-arrow square after target cone inclusion. -/
def laurentMovement :=
  (laurentSquareHomotopy g).postcomp
    (mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))

/-- The target positive-leg comparison preceded by the original base scheme-arrow map. -/
def newPositive :=
  ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    (plusHomotopy X)).cast rfl (Category.assoc _ _ _).symm).postcomp
      (mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))

/-- The previously proved geometric positive-chart pasting retains its full cone-image track. -/
def positivePasting :
    ((positiveMovement g).trans (polynomialMovement g)).RelHomotopy
      ((oldPositive g).symm.trans ((laurentMovement g).trans (newPositive g))) := by
  simpa only [plusInputLeftTrack, plusInputRightTrack,
    Homotopy.postcomp_trans, Homotopy.postcomp_symm, positiveMovement, polynomialMovement,
    oldPositive, laurentMovement, newPositive] using
    (plusInputPasting g).postcomp
      (mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))

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
      mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))
    (zeroHom _ _) :=
  (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y) ≫
    boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (mappingConeHomotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))).cast (by
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
      mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))
    (zeroHom _ _) :=
  (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
    boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
    (mappingConeHomotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))).cast (by
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
    (mappingCone (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X))))
  have J : (oldCone g).RelHomotopy
      (((polynomialMovement g).trans (newCone g)).trans Z) := by
    refine ((Homotopy.Square.interchange (polynomialSquareHomotopy g)
      (mappingConeHomotopy
        (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))).toBoundary).ofLevels
      _ _ ?_ ?_
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
      mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))
    (zeroHom _ _) :=
  ((InputIdentityPositive.sourceNull Y).postcomp
    (InputIdentityPositive.coneMap g)).cast (by
    apply Topology.LoopPrespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl) (by
      apply Topology.LoopPrespectrum.Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      exact (InputIdentityPositive.coneMap g).map_point n)

/-- The original target-fiber Laurent nullhomotopy preceded by actual base scheme-arrow change. -/
def originalNewNull : Homotopy
    ((boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection.app X)) ≫
      mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))
    (zeroHom _ _) :=
  (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    (InputIdentityPositive.sourceNull X)).cast (Category.assoc _ _ _).symm rfl

/-- Every original target-null coordinate is its unchanged positive leg and cone cylinder. -/
lemma originalNewNull_level (n : ℕ) :
    (originalNewNull g).level n = ((newPositive g).trans (newCone g)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level]
  change ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    ((plusHomotopy X).postcomp
      (mappingConeInclusion (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X))))).trans
      (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
        (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (mappingConeHomotopy
            (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)))))).level n = _
  apply Homotopy.trans_level_congr <;> rfl

/-- Each mapped old-null coordinate retains the positive leg and actual cone-square map. -/
lemma originalOldNull_level (n : ℕ) :
    (originalOldNull g).level n =
      ((oldPositive g).trans ((positiveMovement g).trans (oldCone g))).level n := by
  simp only [originalOldNull, Homotopy.cast_level, InputIdentityPositive.sourceNull,
    Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    rfl
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    rfl

/-- The two unchanged Laurent nullhomotopies compare along the actual Laurent scheme-arrow track. -/
def originalNullComparison :
    (originalOldNull g).RelHomotopy ((laurentMovement g).trans (originalNewNull g)) := by
  refine (pastedNullComparison g).ofLevels _ _ (originalOldNull_level g) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level g n


/-- The strict positive inclusion preserves the whole original old positive track. -/
theorem oldPositive_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (oldPositive g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputNull.oldPositive g) := by
  intro s
  rfl

/-- The strict positive inclusion preserves the actual moving positive chart. -/
theorem positiveMovement_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (positiveMovement g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputNull.positiveMovement g) := by
  intro s
  rfl

/-- The original polynomial scheme-arrow movement is unchanged at every time. -/
theorem polynomialMovement_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (polynomialMovement g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputNull.polynomialMovement g) := by
  intro s
  rfl

/-- The original common Laurent movement is unchanged at every time. -/
theorem laurentMovement_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (laurentMovement g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputNull.laurentMovement g) := by
  intro s
  rfl

/-- The strict positive inclusion preserves the whole original new positive track. -/
theorem newPositive_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (newPositive g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputNull.newPositive g) := by
  intro s
  rfl

/-- The old cone cylinder keeps exactly the same original cylinder coordinate. -/
theorem oldCone_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (oldCone g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputNull.oldCone g) := by
  intro s
  rfl

/-- The new cone cylinder keeps exactly the same original cylinder coordinate. -/
theorem newCone_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (newCone g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputNull.newCone g) := by
  intro s
  rfl

/-- The full supplied positive geometric pasting has its exact original cone image. -/
theorem positivePasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (positivePasting g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputNull.positivePasting g) := by
  unfold positivePasting InputNull.positivePasting
  apply Homotopy.RelHomotopy.MappedAt.transport
  all_goals try simp only [plusInputLeftTrack,
    plusInputRightTrack, Homotopy.postcomp_trans, Homotopy.postcomp_symm,
    positiveMovement, polynomialMovement, oldPositive, laurentMovement, newPositive,
    InputNull.positiveMovement, InputNull.polynomialMovement,
    InputNull.oldPositive, InputNull.laurentMovement,
    InputNull.newPositive]
  intro r s
  rfl

/-- Every original associator and cancellation coordinate is retained in the positive pasting. -/
theorem straightPositivePasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (straightPositivePasting g).MappedAt
      (InputIdentityPositive.inclusion X) n x
      (InputNull.straightPositivePasting g) := by
  have hA := oldPositive_mapped g n x
  have hB := positiveMovement_mapped g n x
  have hQ := polynomialMovement_mapped g n x
  have hT := (laurentMovement_mapped g n x).trans (newPositive_mapped g n x)
  exact (hA.transAssoc hB hQ).trans
    ((hA.refl.hcomp (positivePasting_mapped g n x)).trans
      ((hA.transAssoc hA.symm hT).symm.trans
        ((hA.reflTransSymm.symm.hcomp hT.refl).trans hT.reflTrans)))

/-- The actual polynomial/cone interchange and its full boundary collapse map to the old one. -/
theorem conePasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (conePasting g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputNull.conePasting g) := by
  unfold conePasting InputNull.conePasting
  apply Homotopy.RelHomotopy.MappedAt.trans
  · intro r s
    rfl
  · exact ((polynomialMovement_mapped g n x).trans (newCone_mapped g n x)).transRefl

/-- The complete original null recipe preserves all its actual relative subdivisions. -/
theorem pastedNullComparison_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (pastedNullComparison g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputNull.pastedNullComparison g) := by
  have hA := oldPositive_mapped g n x
  have hB := positiveMovement_mapped g n x
  have hQ := polynomialMovement_mapped g n x
  have hE := oldCone_mapped g n x
  have hG := newCone_mapped g n x
  have hL := laurentMovement_mapped g n x
  have hF := newPositive_mapped g n x
  exact (hA.transAssoc hB hE).symm.trans
    (((hA.trans hB).refl.hcomp (conePasting_mapped g n x)).trans
      (((hA.trans hB).transAssoc hQ hG).symm.trans
        (((straightPositivePasting_mapped g n x).hcomp hG.refl).trans
          (hL.transAssoc hF hG))))

/-- The chosen original null comparison is literally the positive one after strict inclusion. -/
theorem originalNullComparison_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (originalNullComparison g).MappedAt (InputIdentityPositive.inclusion X) n x
      (InputNull.originalNullComparison g) :=
  pastedNullComparison_mapped g n x

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityPositiveNull

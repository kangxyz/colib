/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputPasting
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassStep
public import Colib.Topology.Prespectrum.PushoutMovingHomotopy
public import Colib.Topology.Prespectrum.ConeHomotopySquare
public import Colib.Topology.Prespectrum.HomotopySquareInterchange
public import Colib.Topology.Prespectrum.HomotopySquareBoundary

/-!
# The independently constructed global raw Bass input map

The genuine original geometric overlap descends through the actual polynomial double cylinder,
Laurent comparison, reduced cone and parameter loops. This constructs `GlobalRawBass.map`
contravariantly for each scheme arrow, including all chart and cylinder values. No strict
functor, identity/composition law, or higher raw tower is asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The target track is the whole original polynomial-span cylinder followed by Bass comparison. -/
theorem inputTargetDescTrack_level (n : ℕ) :
    (inputTargetDescTrack g).level n =
      ((HomotopyPushout.mapSquareHomotopy
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
        (boundedAboveFlatPerfectPullbackPrespectrumMap g)
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
        (polynomialSquareHomotopy g)
          (polynomialSquareHomotopy g)).postcomp
          (comparison X)).level n := by
  simp only [inputTargetDescTrack, Homotopy.cast_level,
    inputTargetTrack, HomotopyPushout.mapSquareHomotopy,
    Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- The source descent equals the literal original Bass comparison followed by Laurent change. -/
theorem inputSourceDesc_eq :
    HomotopyPushout.desc
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app Y) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (minus.app Y) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
      (inputSourceDescTrack g) =
    comparison Y ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g) := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- The target descent equals the original polynomial-span map followed by Bass comparison. -/
theorem inputTargetDesc_eq :
    HomotopyPushout.desc
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (minus.app X))
      (inputTargetDescTrack g) =
    spanMap g ≫ comparison X := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (inputTargetDescTrack_level g n) (s, x)

/-- The actual geometric moving square descends to the two unchanged scheme-arrow composites. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassInputMap.lean:82-132"
  "adaptation" "Original scheme-arrow Laurent comparison with all signed and cylinder values"]
def inputComparisonHomotopy :
    Homotopy (comparison Y ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
      (spanMap g ≫ comparison X) :=
  (HomotopyPushout.descSquareHomotopy
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
    (plusSquareHomotopy g) (minusSquareHomotopy g)
    (inputDescPasting g).toSquare).cast
      (inputSourceDesc_eq g) (inputTargetDesc_eq g)

/-- The left polynomial endpoint moves through its unchanged positive Laurent square. -/
theorem inputComparisonHomotopy_inl (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (polynomial.obj Y).toRingedSpace)).space n) :
    (inputComparisonHomotopy g).level n
      (r, (HomotopyPushout.inl
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))).map n x) =
      (plusSquareHomotopy g).level n (r, x) := rfl

/-- The right polynomial endpoint moves through its distinct negative Laurent square. -/
theorem inputComparisonHomotopy_inr (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (polynomial.obj Y).toRingedSpace)).space n) :
    (inputComparisonHomotopy g).level n
      (r, (HomotopyPushout.inr
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))).map n x) =
      (minusSquareHomotopy g).level n (r, x) := rfl

/-- The whole actual cylinder retains the square constructed from the proved geometric pasting. -/
theorem inputComparisonHomotopy_cylinder (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (inputComparisonHomotopy g).level n
      (r, HomotopyPushout.cylinder
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y)) n (s, x)) =
      (inputDescPasting g).toSquare.level n (r, (s, x)) := rfl

/-- The original relative comparison is recovered on every collapsed parameter-square point. -/
theorem inputComparisonHomotopy_collapse (n : ℕ)
    (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (inputComparisonHomotopy g).level n
      ((Topology.ThreeSideSquare.collapse z).1, HomotopyPushout.cylinder
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y)) n
          ((Topology.ThreeSideSquare.collapse z).2, x)) =
      (inputDescPasting g).level n (z.1, (z.2, x)) :=
  (inputDescPasting g).toSquare_collapse n z x

/-- The genuine comparison-map homotopy induces an actual map of the original Bass square cones. -/
def coneMap :
    mappingCone (comparison Y) ⟶
      mappingCone (comparison X) :=
  mappingConeSquareMap _ _ (spanMap g)
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (inputComparisonHomotopy g)

/-- Parameter-correct looping gives a map between the actual one-step Bass spectra. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassInputMap.lean:134-195"
  "adaptation" "Original one-step map along an arbitrary scheme arrow, retaining its loop time"]
def map : step Y ⟶ step X :=
  parameterLoopingMap (coneMap g)

/-- The literal Laurent inclusion commutes with the actual scheme-arrow cone map. -/
lemma coneMap_inclusion :
    mappingConeInclusion (comparison Y) ≫
      coneMap g =
      boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g) ≫
        mappingConeInclusion (comparison X) :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- The whole cone cylinder retains the actual input comparison and target cone null track. -/
lemma coneMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (HomotopyPushout.prespectrum
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))).space n) :
    (coneMap g).map n
      (ReducedMappingCone.cylinder _ _ ((comparison Y).map n)
        (s, x)) =
    (((inputComparisonHomotopy g).postcomp
      (mappingConeInclusion (comparison X))).trans
      (Homotopy.precomp (spanMap g)
        (mappingConeHomotopy (comparison X)))).level n (s, x) := rfl

/-- The unchanged positive source leg maps to its literal polynomial endpoint. -/
theorem sourceLeg_spanMap :
    sourceLeg Y ≫ spanMap g =
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap
          (polynomial.map g)) ≫
          HomotopyPushout.inl
            (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
            (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)) := by
  unfold sourceLeg
  rw [Category.assoc, inl_spanMap, Category.assoc]

/-- The original geometric polynomial square moves the unchanged positive source leg. -/
def sourceLegInputHomotopy :
    Homotopy
      (sourceLeg Y ≫ spanMap g)
      (boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
        sourceLeg X) :=
  ((polynomialSquareHomotopy g).postcomp
    (HomotopyPushout.inl
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)))).cast
      (sourceLeg_spanMap g).symm (Category.assoc _ _ _)

/-- Source movement and the original raw cone contraction keep their parameters independent. -/
def sourceLegInputConeSquare :=
  Homotopy.Square.interchange (sourceLegInputHomotopy g)
    (mappingConeHomotopy (comparison X))

theorem sourceLegInputConeSquare_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (sourceLegInputConeSquare g).level n (r, (s, x)) =
      (mappingConeHomotopy (comparison X)).level n
        (s, (sourceLegInputHomotopy g).level n (r, x)) := rfl

/-- The positive source-leg movement retains its complete original cone boundary. -/
def sourceLegInputConeBoundary :=
  (sourceLegInputConeSquare g).toBoundary

/-- Parameter looping applies the same raw cone map at each independent loop coordinate. -/
theorem map_apply (n : ℕ) (s : unitInterval)
    (x : (parameterLooping
      (mappingCone (comparison Y))).space n) :
    Path.toContinuousMap ((map g).map n x) s =
      (coneMap g).map n (Path.toContinuousMap x s) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass

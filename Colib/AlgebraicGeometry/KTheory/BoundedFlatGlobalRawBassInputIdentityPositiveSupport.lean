/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputMap
public import Colib.Topology.Prespectrum.NullLoopNaturality

/-!
# The literal positive-cone support of the global raw identity seed

The unchanged global source-null and forward seed factor through the actual positive-chart
cone. Its strict inclusion retains every original cylinder time. The original raw input map
also preserves this support, without modifying its chart comparison or either null leg.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace
open scoped Topology unitInterval
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityPositive
variable (X : Scheme.{u})

/-- The genuine positive-chart arrow whose cone supports the original seed. -/
abbrev chart := boundedAboveFlatPerfectPullbackPrespectrumMap (plus.app X)

/-- The strict positive-chart square uses the actual span inclusion and Laurent identity. -/
def inclusionSquare : Arrow.mk (chart X) ⟶ Arrow.mk (comparison X) :=
  Arrow.homMk
    (HomotopyPushout.inl (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))) (𝟙 _)
    (by
      apply Topology.LoopPrespectrum.Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      rfl)

/-- The positive cone enters through its strict square, with no extra path segment. -/
def inclusion : mappingCone (chart X) ⟶ mappingCone (comparison X) :=
  mappingConeMap (inclusionSquare X)

/-- The supported Laurent inclusion is literally the original one. -/
theorem inclusion_inclusion :
    mappingConeInclusion (chart X) ≫ inclusion X = mappingConeInclusion (comparison X) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

/-- Every positive cylinder point retains its original height and polynomial point. -/
theorem inclusion_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (polynomial.obj X).toRingedSpace)).space n) :
    (inclusion X).map n (ReducedMappingCone.cylinder _ _ ((chart X).map n) (s, x)) =
      ReducedMappingCone.cylinder _ _ ((comparison X).map n)
        (s, (HomotopyPushout.inl (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))).map n x) := rfl

/-- Both original null legs already live in the positive cone. -/
def sourceNull : Homotopy
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection.app X) ≫
      mappingConeInclusion (chart X))
    (zeroHom (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))
      (mappingCone (chart X))) :=
  ((plusHomotopy X).postcomp (mappingConeInclusion (chart X))).trans
    (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
      (mappingConeHomotopy (chart X)))

/-- The complete supported null evaluates to the fixed original two-leg source-null. -/
theorem sourceNull_factor (n : ℕ) :
    ((sourceNull X).postcomp (inclusion X)).level n =
      (GlobalRawBass.sourceNull X).level n := by
  change ((((plusHomotopy X).postcomp (mappingConeInclusion (chart X))).trans
    (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
      (mappingConeHomotopy (chart X)))).postcomp (inclusion X)).level n = _
  rw [Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change _ = (sourceLegNull X).level n (s, x)
    rw [sourceLegNull_apply]
    rfl

/-- An auxiliary factor of the existing transition, using its original unit and null word. -/
def seed : originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⟶
    parameterLooping (mappingCone (chart X)) :=
  ((unitHomotopy X).postcomp (mappingConeInclusion (chart X))).nullLoopMap (sourceNull X)

/-- The actual positive seed maps exactly to the fixed global transition. -/
theorem seed_factor : seed X ≫ parameterLoopingMap (inclusion X) = transition X := by
  have h := Homotopy.nullLoopMap_naturality
    (𝟙 (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))) (inclusion X)
    ((unitHomotopy X).postcomp (mappingConeInclusion (chart X)))
    ((unitHomotopy X).postcomp (mappingConeInclusion (comparison X)))
    (sourceNull X) (GlobalRawBass.sourceNull X)
    (fun _ ↦ rfl) (sourceNull_factor X)
  simpa only [Category.id_comp, seed, transition] using h

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual positive input cone map uses the original positive geometric square. -/
def coneMap : mappingCone (chart Y) ⟶ mappingCone (chart X) :=
  mappingConeSquareMap (chart Y) (chart X)
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g)) (plusSquareHomotopy g)

/-- Both halves of the actual positive input null factor to the fixed whole input null. -/
theorem coneMapNull_factor (n : ℕ) :
    ((mappingConeSquareNullHomotopy (chart Y) (chart X)
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
      (plusSquareHomotopy g)).postcomp (inclusion X)).level n =
    (Homotopy.precomp
      (HomotopyPushout.inl (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app Y)))
      (mappingConeSquareNullHomotopy (comparison Y) (comparison X) (spanMap g)
        (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
        (inputComparisonHomotopy g))).level n := by
  simp only [mappingConeSquareNullHomotopy, Homotopy.postcomp_trans, Homotopy.precomp_trans]
  apply Homotopy.trans_level_congr <;> rfl

/-- The original raw cone map preserves the strict positive support on all cone points. -/
theorem coneMap_factor :
    inclusion Y ≫ GlobalRawBass.coneMap g = coneMap g ≫ inclusion X := by
  apply mappingCone_hom_ext
  · apply Topology.LoopPrespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl
  · intro n s x
    exact (DFunLike.congr_fun (coneMapNull_factor g n) (s, x)).symm

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityPositive

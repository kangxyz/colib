/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineBassSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitHomotopy
public import Colib.Topology.Prespectrum.NullLoopNaturality
public import Colib.Topology.Prespectrum.MappingCone

/-! # The actual raw bounded-flat Bass transition

The forward Laurent unit and positive-source cone null form the original conjugated loop.
Implementation provenance: Quillen `Affine/BoundedFlatBassStep.lean:28-85`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual Laurent scalar gives the original bounded-flat Laurent-unit self-homotopy. -/
def boundedAboveFlatLaurentUnitHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection R))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection R)) :=
  boundedAboveFlatPerfectUnitHomotopy (laurentProjection R) (laurentCoordinate R)

/--
The parameter-correct desuspended actual square cone for this affine polynomial/Laurent diagram.
-/
def boundedAboveFlatAffineBassStep (R : CommRingCat.{u}) : LoopPrespectrum :=
  parameterLooping (mappingCone (boundedAboveFlatBassSquareComparison R))

/-- The source leg into the polynomial-chart homotopy pushout, using original bounded-flat
      pullback. -/
def boundedAboveFlatBassSourceLeg (R : CommRingCat.{u}) :
    originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) ⟶
      HomotopyPushout.prespectrum
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R)) :=
  boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R) ≫ HomotopyPushout.inl _ _

lemma boundedAboveFlatBassSourceLeg_comparison (R : CommRingCat.{u}) :
    boundedAboveFlatBassSourceLeg R ≫ boundedAboveFlatBassSquareComparison R =
      boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurentToPolynomial R) := by
  unfold boundedAboveFlatBassSourceLeg boundedAboveFlatBassSquareComparison
  rw [Category.assoc, HomotopyPushout.inl_desc]

/-- The original Laurent map becomes genuinely null after the actual square-cone inclusion. -/
def boundedAboveFlatBassLaurentNullHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection R) ≫
      mappingConeInclusion
      (boundedAboveFlatBassSquareComparison R))
      (LoopPrespectrum.zeroHom
        (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
        (mappingCone (boundedAboveFlatBassSquareComparison R))) := by
  have N := Homotopy.precomp (boundedAboveFlatBassSourceLeg R) (mappingConeHomotopy
      (boundedAboveFlatBassSquareComparison R))
  change Homotopy ((boundedAboveFlatBassSourceLeg R ≫ boundedAboveFlatBassSquareComparison R) ≫
    mappingConeInclusion (boundedAboveFlatBassSquareComparison R))
      (LoopPrespectrum.zeroHom _ _) at N
  rw [boundedAboveFlatBassSourceLeg_comparison] at N
  exact ((boundedAboveFlatLaurentPlusHomotopy R).postcomp (mappingConeInclusion
      (boundedAboveFlatBassSquareComparison R))).trans N

/-- The first half of the original null is the positive geometric split track in the cone. -/
theorem boundedAboveFlatBassLaurentNullHomotopy_first_half (R : CommRingCat.{u}) (n : ℕ)
    (t : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space n) :
    (boundedAboveFlatBassLaurentNullHomotopy R).level n
      (⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x) =
    (mappingConeInclusion (boundedAboveFlatBassSquareComparison R)).map n
      ((boundedAboveFlatLaurentPlusHomotopy R).level n (t, x)) := by
  change ((((boundedAboveFlatLaurentPlusHomotopy R).postcomp
    (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))).levelHomotopy n).trans
      (((Homotopy.precomp (boundedAboveFlatBassSourceLeg R)
        (mappingConeHomotopy (boundedAboveFlatBassSquareComparison R))).cast
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun h => h ≫ mappingConeInclusion (boundedAboveFlatBassSquareComparison R))
              (boundedAboveFlatBassSourceLeg_comparison R)))
          (show boundedAboveFlatBassSourceLeg R ≫ LoopPrespectrum.zeroHom _ _ =
            LoopPrespectrum.zeroHom _ _ from rfl)).levelHomotopy
            n))
          (⟨(t : ℝ) / 2, _⟩, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · change (mappingConeInclusion (boundedAboveFlatBassSquareComparison R)).map n
      ((boundedAboveFlatLaurentPlusHomotopy R).level n (⟨2 * ((t : ℝ) / 2), _⟩, x)) = _
    congr 2
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      ring
    · rfl
  · rename_i ht
    exfalso
    apply ht
    change (t : ℝ) / 2 ≤ 1 / 2
    linarith [t.2.2]

/-- The second half is the actual cone cylinder on the original positive source-leg image. -/
theorem boundedAboveFlatBassLaurentNullHomotopy_second_half (R : CommRingCat.{u}) (n : ℕ)
    (t : unitInterval)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space n) :
    (boundedAboveFlatBassLaurentNullHomotopy R).level n
      (⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x) =
    (mappingConeHomotopy (boundedAboveFlatBassSquareComparison R)).level n
      (t, (boundedAboveFlatBassSourceLeg R).map n x) := by
  change ((((boundedAboveFlatLaurentPlusHomotopy R).postcomp
    (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))).levelHomotopy n).trans
      (((Homotopy.precomp (boundedAboveFlatBassSourceLeg R)
        (mappingConeHomotopy (boundedAboveFlatBassSquareComparison R))).cast
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun h => h ≫ mappingConeInclusion (boundedAboveFlatBassSquareComparison R))
              (boundedAboveFlatBassSourceLeg_comparison R)))
          (show boundedAboveFlatBassSourceLeg R ≫ LoopPrespectrum.zeroHom _ _ =
            LoopPrespectrum.zeroHom _ _ from rfl)).levelHomotopy
            n))
          (⟨((t : ℝ) + 1) / 2, _⟩, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · rename_i ht
    have ht0 : t = 0 := by
      apply Subtype.ext
      change (t : ℝ) = 0
      have hh : ((t : ℝ) + 1) / 2 ≤ 1 / 2 := ht
      linarith [t.2.1]
    subst t
    have hs : (⟨2 * (((0 : ℝ) + 1) / 2), by norm_num⟩ : unitInterval) = 1 := by
      apply Subtype.ext
      norm_num
    change (mappingConeInclusion (boundedAboveFlatBassSquareComparison R)).map n
      ((boundedAboveFlatLaurentPlusHomotopy R).level n
        ((⟨2 * (((0 : ℝ) + 1) / 2), by norm_num⟩ : unitInterval), x)) = _
    rw [hs, (boundedAboveFlatLaurentPlusHomotopy R).at_one]
    exact ((mappingConeHomotopy (boundedAboveFlatBassSquareComparison R)).at_zero n
      ((boundedAboveFlatBassSourceLeg R).map n x)).symm
  · change (mappingConeHomotopy (boundedAboveFlatBassSquareComparison R)).level n
      (⟨2 * (((t : ℝ) + 1) / 2) - 1, _⟩, (boundedAboveFlatBassSourceLeg R).map n x) = _
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      ring
    · rfl

/-- The actual affine Bass transition: conjugate the Laurent-unit loop by the original cone
  nullhomotopy.
The target uses the proved parameter-correct loop structure. -/
def boundedAboveFlatAffineBassTransition (R : CommRingCat.{u}) :
    originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace) ⟶
      boundedAboveFlatAffineBassStep R :=
  ((boundedAboveFlatLaurentUnitHomotopy R).postcomp (mappingConeInclusion
      (boundedAboveFlatBassSquareComparison R))).nullLoopMap
    (boundedAboveFlatBassLaurentNullHomotopy R)

/--
The whole original transition loop retains its supplied Laurent action and both nullhomotopy legs.
-/
theorem boundedAboveFlatAffineBassTransition_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)).space n)
    (s : unitInterval) :
    Path.toContinuousMap ((boundedAboveFlatAffineBassTransition R).map n x) s =
      (((boundedAboveFlatLaurentUnitHomotopy R).postcomp
        (mappingConeInclusion (boundedAboveFlatBassSquareComparison R))).conjugateToZero
          (boundedAboveFlatBassLaurentNullHomotopy R)).level n (s, x) := rfl


end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/BoundedFlatBassStep.lean:28-85"
  "adaptation" "Original forward-unit, positive-source null, and parameter-looped Bass transition"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatLaurentUnitHomotopy
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineBassStep
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatBassSourceLeg
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatBassLaurentNullHomotopy
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineBassTransition

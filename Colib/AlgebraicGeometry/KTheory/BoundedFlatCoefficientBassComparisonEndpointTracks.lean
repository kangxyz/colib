/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassSquareComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientLaurentUnitSquares
public import Colib.Topology.Prespectrum.PushoutHomotopySquare
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! # Literal endpoints for the moving Bass comparison

Both Laurent charts retain the two routes in the actual comparison diagram.
The source and target descents are the unchanged composites of the raw Bass
square with the coefficient and polynomial-span maps, respectively. This
constructs the endpoint tracks only, not the relative filler relating them.

Source: Quillen `BoundedFlat/CoefficientBassMap.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`: 134–149, 166–181, 206–224,
270–286, and 302–357.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (g : a ⟶ b)

/-- Paste the original plus Laurent square and the original polynomial square. -/
def boundedAboveFlatCoefficientPlusLeftTrack :=
  ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
    (boundedAboveFlatCoefficientPlusSquareHomotopy P g)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((boundedAboveFlatCoefficientPolynomialSquareHomotopy P g).postcomp
      (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentPlus P b)))

/-- The plus route through the common original Laurent projection square. -/
def boundedAboveFlatCoefficientPlusRightTrack :=
  ((boundedAboveFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map
      g)))).symm.trans
    ((boundedAboveFlatCoefficientLaurentSquareHomotopy P g).trans
      ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P g))
        (boundedAboveFlatCoefficientLaurentPlusHomotopy P b)).cast rfl (Category.assoc _ _ _).symm))

/-- Paste the original minus Laurent square and the original polynomial square. -/
def boundedAboveFlatCoefficientMinusLeftTrack :=
  ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
    (boundedAboveFlatCoefficientMinusSquareHomotopy P g)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((boundedAboveFlatCoefficientPolynomialSquareHomotopy P g).postcomp
      (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus P b)))

/-- The minus route through the common original Laurent projection square. -/
def boundedAboveFlatCoefficientMinusRightTrack :=
  ((boundedAboveFlatCoefficientLaurentMinusHomotopy P a).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map
      g)))).symm.trans
    ((boundedAboveFlatCoefficientLaurentSquareHomotopy P g).trans
      ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P g))
        (boundedAboveFlatCoefficientLaurentMinusHomotopy P b)).cast rfl
          (Category.assoc _ _ _).symm))

/-- The right-associated target cylinder retains both original polynomial-square tracks. -/
def boundedAboveFlatCoefficientBassTargetTrack :=
  ((boundedAboveFlatCoefficientPolynomialSquareHomotopy P g).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentPlus P b))).trans
    (((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P g))
      (boundedAboveFlatCoefficientBassSquareHomotopy P b)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
      ((boundedAboveFlatCoefficientPolynomialSquareHomotopy P g).symm.postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus P b))))

/-- The precise outer left association required by the moving-square conversion. -/
def boundedAboveFlatCoefficientBassPastedTrack :=
  (((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
    (boundedAboveFlatCoefficientPlusSquareHomotopy P g)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    (boundedAboveFlatCoefficientBassTargetTrack P g)).trans
    ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
      (boundedAboveFlatCoefficientMinusSquareHomotopy P g)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).symm

/-- Regroup the source endpoint maps to the literal span-comparison composition maps. -/
def boundedAboveFlatCoefficientBassSourceDescTrack :=
  ((boundedAboveFlatCoefficientBassSquareHomotopy P a).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap
      (coefficientMap P ((laurentUnderFunctor R).map g)))).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Regroup the target endpoints to the literal polynomial-coefficient composite maps. -/
def boundedAboveFlatCoefficientBassTargetDescTrack :=
  (boundedAboveFlatCoefficientBassTargetTrack P g).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The exact boundary now uses the untransported precompositions of both Laurent squares. -/
def boundedAboveFlatCoefficientBassPastedDescTrack :=
  ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
    (boundedAboveFlatCoefficientPlusSquareHomotopy P g)).trans
      (boundedAboveFlatCoefficientBassTargetDescTrack P g)).trans
    (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
      (boundedAboveFlatCoefficientMinusSquareHomotopy P g)).symm

/-- The target track is the whole original polynomial-span cylinder followed by Bass comparison. -/
theorem boundedAboveFlatCoefficientBassTargetDescTrack_level (n : ℕ) :
    (boundedAboveFlatCoefficientBassTargetDescTrack P g).level n =
      ((HomotopyPushout.mapSquareHomotopy
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P b))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P b))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (coefficientMap P g))
        (boundedAboveFlatPerfectPullbackPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map g)))
        (boundedAboveFlatPerfectPullbackPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map g)))
        (boundedAboveFlatCoefficientPolynomialSquareHomotopy P g)
          (boundedAboveFlatCoefficientPolynomialSquareHomotopy P g)).postcomp
          (boundedAboveFlatCoefficientBassSquareComparison P b)).level n := by
  simp only [boundedAboveFlatCoefficientBassTargetDescTrack, Homotopy.cast_level,
    boundedAboveFlatCoefficientBassTargetTrack, HomotopyPushout.mapSquareHomotopy,
    Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- The source descent equals the literal original Bass comparison followed by Laurent change. -/
theorem boundedAboveFlatCoefficientBassSourceDesc_eq :
    HomotopyPushout.desc
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentPlus P a) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap
          (coefficientMap P ((laurentUnderFunctor R).map g)))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus P a) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap
          (coefficientMap P ((laurentUnderFunctor R).map g)))
      (boundedAboveFlatCoefficientBassSourceDescTrack P g) =
    boundedAboveFlatCoefficientBassSquareComparison P a ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map g)) := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- The target descent equals the original polynomial-span map followed by Bass comparison. -/
theorem boundedAboveFlatCoefficientBassTargetDesc_eq :
    HomotopyPushout.desc
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
      (boundedAboveFlatPerfectPullbackPrespectrumMap
        (coefficientMap P ((polynomialUnderFunctor R).map g)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurentPlus P b))
      (boundedAboveFlatPerfectPullbackPrespectrumMap
        (coefficientMap P ((polynomialUnderFunctor R).map g)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (laurentMinus P b))
      (boundedAboveFlatCoefficientBassTargetDescTrack P g) =
    boundedAboveFlatCoefficientPolynomialSpanMap P g
      ≫ boundedAboveFlatCoefficientBassSquareComparison P b
      := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (boundedAboveFlatCoefficientBassTargetDescTrack_level P g n) (s, x)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassMap.lean:302-357"
  "adaptation" "Actual target cylinder and both original endpoint descent equalities."]
  boundedAboveFlatCoefficientBassTargetDescTrack_level
  boundedAboveFlatCoefficientBassSourceDesc_eq
  boundedAboveFlatCoefficientBassTargetDesc_eq

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenCofinality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTower
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedPolynomialLaurentTransport
public import Colib.AlgebraicGeometry.KTheory.Bass.SupportedGroups
public import Colib.KTheory.Waldhausen.Iterated.SmallModelComparison

/-!
Source in `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/`:
`CoefficientSupportedKZeroComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original supported K-zero at the actual native stage-zero bottom

Original supported evaluation, bounded-flat inclusion and the actual small-model
K/stable comparison identify the original supported perfect K-zero functor with
the finite stage-zero group. Naturality retains every original coefficient pair
square. The only compactness used here concerns the ambient scheme. Successor
bottoms and invertibility of supported transitions are separate assertions.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Actual supported section evaluation followed by the original perfect inclusion comparison. -/
def boundedAboveFlatCoefficientSupportedPerfectKEquiv (a : Under R) (n : ℕ) :
    (boundedAboveFlatCoefficientSupportedModel f a).obj.waldhausen.K n ≃*
      PerfectSupportedK (schemeMap f a) n := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  exact (boundedAboveFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).trans
    (boundedAboveFlatPerfectSupportedKEquiv (schemeMap f a) n)

/-- The original supported evaluation preserves the exact coefficient pullback K-map. -/
theorem boundedAboveFlatCoefficientSupportedPerfectKEquiv_naturality
    {a b : Under R} (g : a ⟶ b) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSupportedModel f a).obj.waldhausen.K n) :
    boundedAboveFlatCoefficientSupportedPerfectKEquiv f b n
        (KMap (boundedAboveFlatCoefficientSupportedModelMap f g).hom.isExact n x) =
      perfectSupportedKPullback
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).map g).unop n
          (boundedAboveFlatCoefficientSupportedPerfectKEquiv f a n x) := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : CompactSpace (space (op Q, b)) := compactSpace_space (op Q, b)
  have he := boundedAboveFlatCoefficientEvaluationKEquiv_natural
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
    (boundedAboveFlatPerfectSupportedWaldhausen (schemeMap f a))
    (boundedAboveFlatCoefficientSupportedSectionEquivalence (schemeMap f a))
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_functor_exact (schemeMap f a))
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact (schemeMap f a))
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f b))
    (boundedAboveFlatPerfectSupportedWaldhausen (schemeMap f b))
    (boundedAboveFlatCoefficientSupportedSectionEquivalence (schemeMap f b))
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_functor_exact (schemeMap f b))
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact (schemeMap f b))
    (boundedAboveFlatCoefficientSupportedModelMap f g).hom.isExact
    (boundedAboveFlatPerfectSupportedPullback_isExact (boundedAboveFlatCoefficientOpenPairMap f g))
    (by
      simp only [boundedAboveFlatCoefficientSupportedSectionEquivalence_functor]
      exact boundedAboveFlatCoefficientSupportedSectionReindexIso
        (schemeMap f a) (schemeMap f b) (𝟙 (op Q), g)
        (coefficientMap P g) (boundedAboveFlatCoefficientOpenSquare f g)) n x
  have hp := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat
    ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).map g).unop n)
    (boundedAboveFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n x)
  exact (congrArg (boundedAboveFlatPerfectSupportedKEquiv (schemeMap f b) n) he).trans hp.symm

/-- Original supported perfect K-zero is the actual stage-zero stable group. -/
def boundedAboveFlatCoefficientSupportedBassBottomZeroIso (a : Under R) :
    (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedKZeroFunctor).obj a ≅
      (boundedAboveFlatCoefficientSupportedBassDiagram f 0 ⋙ stableHomotopyFunctor 0).obj a :=
  ((boundedAboveFlatCoefficientSupportedPerfectKEquiv f a 0).symm.toAdditive.trans
    (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedModel f a) 0)).toAddCommGrpIso

/-- Every original coefficient pair pullback is preserved by the stage-zero comparison. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedBassBottomZeroIso_naturality
    {a b : Under R} (g : a ⟶ b) :
    (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedKZeroFunctor).map g ≫
        (boundedAboveFlatCoefficientSupportedBassBottomZeroIso f b).hom =
      (boundedAboveFlatCoefficientSupportedBassBottomZeroIso f a).hom ≫
        (boundedAboveFlatCoefficientSupportedBassDiagram f 0 ⋙ stableHomotopyFunctor 0).map g := by
  ext x
  let y := (boundedAboveFlatCoefficientSupportedPerfectKEquiv f a 0).symm x.toMul
  have hy : boundedAboveFlatCoefficientSupportedPerfectKEquiv f a 0 y = x.toMul :=
    (boundedAboveFlatCoefficientSupportedPerfectKEquiv f a 0).apply_symm_apply x.toMul
  have hn := boundedAboveFlatCoefficientSupportedPerfectKEquiv_naturality f g 0 y
  rw [hy] at hn
  have hi := congrArg (boundedAboveFlatCoefficientSupportedPerfectKEquiv f b 0).symm hn
  rw [MulEquiv.symm_apply_apply] at hi
  change smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedModel f b) 0
      (Additive.ofMul ((boundedAboveFlatCoefficientSupportedPerfectKEquiv f b 0).symm
        (perfectSupportedKPullback
          ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).map g).unop 0 x.toMul))) =
    (stableHomotopyFunctor 0).map (prespectrumMap (boundedAboveFlatCoefficientSupportedModelMap
      f g))
      (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedModel f a) 0 (Additive.ofMul y))
  rw [← hi]
  exact smallModelKStableEquiv_naturality (boundedAboveFlatCoefficientSupportedModelMap f g) 0 y

/-- The original supported K-zero functor naturally computes the actual finite bottom. -/
def boundedAboveFlatCoefficientSupportedBassBottomZeroNatIso :
    boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedKZeroFunctor ≅
      boundedAboveFlatCoefficientSupportedBassDiagram f 0 ⋙ stableHomotopyFunctor 0 :=
  NatIso.ofComponents (boundedAboveFlatCoefficientSupportedBassBottomZeroIso f)
    (fun g ↦ boundedAboveFlatCoefficientSupportedBassBottomZeroIso_naturality f g)

attribute [colib_ref "quillen" "CoefficientSupportedKZeroComparison.lean:37"
  "adaptation" "Original supported finite comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedPerfectKEquiv
attribute [colib_ref "quillen" "CoefficientSupportedKZeroComparison.lean:45"
  "adaptation" "Original supported finite comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedPerfectKEquiv_naturality
attribute [colib_ref "quillen" "CoefficientSupportedKZeroComparison.lean:79"
  "adaptation" "Original supported finite comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedBassBottomZeroIso
attribute [colib_ref "quillen" "CoefficientSupportedKZeroComparison.lean:87"
  "adaptation" "Original supported finite comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedBassBottomZeroIso_naturality
attribute [colib_ref "quillen" "CoefficientSupportedKZeroComparison.lean:111"
  "adaptation" "Original supported finite comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedBassBottomZeroNatIso

end AlgebraicGeometry.Scheme.Modules

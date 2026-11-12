/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedKZeroComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassKZeroComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SupportedForget

/-!
Source:
`PerfectComplexes/BoundedFlat/CoefficientSupportedKZeroForgetComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The original supported-to-ambient map at the native zero bottom

The actual supported evaluation square preserves the original support inclusion on every
K-group. At degree zero it compares the existing supported and ambient finite-bottom
isomorphisms, including the ambient normalized perfect evaluation. Only ambient compactness
is needed. No injectivity of the support-forgetting map is used.
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
  [IsOpenImmersion f.left]

/-- The actual evaluation square preserves the bounded-flat support inclusion on all K-groups. -/
theorem boundedAboveFlatCoefficientSupportedSectionKEquiv_forget (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSupportedModel f a).obj.waldhausen.K n) :
    boundedAboveFlatCoefficientSectionKEquiv (op Q, a) n
        (KMap (boundedAboveFlatCoefficientSupportedForgetModelMap f a).hom.isExact n x) =
      boundedAboveFlatPerfectSupportedForgetKMap (schemeMap f a) n
        (boundedAboveFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n x) := by
  exact boundedAboveFlatCoefficientEvaluationKEquiv_natural
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
    (boundedAboveFlatPerfectSupportedWaldhausen (schemeMap f a))
    (boundedAboveFlatCoefficientSupportedSectionEquivalence (schemeMap f a))
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_functor_exact (schemeMap f a))
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact (schemeMap f a))
    (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a))
    (boundedAboveFlatPerfectWaldhausen (space (op Q, a)).toRingedSpace)
    (boundedAboveFlatCoefficientSectionEquivalence (op Q, a))
    (boundedAboveFlatCoefficientOriginalEvaluation_exact (op Q, a))
    (boundedAboveFlatCoefficientSectionEquivalence_inverse_exact (op Q, a))
    (boundedAboveFlatCoefficientSupportedForgetModelMap f a).hom.isExact
    (boundedAboveFlatPerfectSupportedForget_isExact (schemeMap f a))
    (by
      simp only [boundedAboveFlatCoefficientSupportedSectionEquivalence_functor]
      exact eqToIso (boundedAboveFlatCoefficientSupportedEvaluation_forget_to_boundedAboveFlat
        f a).symm)
    n x

variable [CompactSpace Q.left]

/-- The literal original perfect support inclusion commutes with the existing K-equivalences. -/
theorem boundedAboveFlatCoefficientSupportedPerfectKEquiv_forget (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSupportedModel f a).obj.waldhausen.K n) :
    boundedAboveFlatCoefficientSectionPerfectKEquiv (op Q, a) n
        (KMap (boundedAboveFlatCoefficientSupportedForgetModelMap f a).hom.isExact n x) =
      perfectSupportedKMap (schemeMap f a) n
        (boundedAboveFlatCoefficientSupportedPerfectKEquiv f a n x) := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  rw [boundedAboveFlatCoefficientSectionPerfectKEquiv_apply,
    boundedAboveFlatCoefficientSupportedSectionKEquiv_forget]
  exact (DFunLike.congr_fun (boundedAboveFlatPerfectSupportedToPerfectKMap_forget
    (schemeMap f a) n) (boundedAboveFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n x)).symm

/-- The original zero-bottom comparisons retain the actual supported-to-ambient model map. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedBassBottomZeroIso_forget (a : Under R) :
    Bass.supportedKZeroForget.app ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
        (boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso Q).hom.app a =
      (boundedAboveFlatCoefficientSupportedBassBottomZeroIso f a).hom ≫
        (stableHomotopyFunctor 0).map ((boundedAboveFlatCoefficientSupportedBassForget f 0).app
          a) := by
  let : IsIso ((stableHomotopyFunctor 0).map
      (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op Q, a))) :=
    boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap_isStableEquivalence (op
      Q, a) 0
  apply (cancel_mono ((stableHomotopyFunctor 0).map
    (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op Q, a)))).mp
  rw [Category.assoc, boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso_evaluation]
  ext x
  obtain ⟨y, hy⟩ := (boundedAboveFlatCoefficientSupportedPerfectKEquiv f a 0).surjective x.toMul
  change originalKStableEquiv (perfectComplexesWaldhausen (space (op Q, a)).toRingedSpace) 0
      (Additive.ofMul (perfectSupportedKMap (schemeMap f a) 0 x.toMul)) =
    (stableHomotopyFunctor 0).map
      (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op Q, a))
      ((stableHomotopyFunctor 0).map
        (prespectrumMap (boundedAboveFlatCoefficientSupportedForgetModelMap f a))
        (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedModel f a) 0
          (Additive.ofMul ((boundedAboveFlatCoefficientSupportedPerfectKEquiv f a 0).symm
            x.toMul))))
  rw [← hy, MulEquiv.symm_apply_apply]
  exact (congrArg (fun z ↦ originalKStableEquiv (perfectComplexesWaldhausen (space (op Q,
    a)).toRingedSpace) 0
      (Additive.ofMul z)) (boundedAboveFlatCoefficientSupportedPerfectKEquiv_forget f a 0
        y).symm).trans
    (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KEquiv (op Q, a) 0
      (KMap (boundedAboveFlatCoefficientSupportedForgetModelMap f a).hom.isExact 0 y) |>.trans
        (congrArg ((stableHomotopyFunctor 0).map
          (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op Q, a)))
          (smallModelKStableEquiv_naturality
            (boundedAboveFlatCoefficientSupportedForgetModelMap f a) 0 y)))


attribute [colib_ref "quillen" "CoefficientSupportedKZeroForgetComparison.lean:33"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedSectionKEquiv_forget
attribute [colib_ref "quillen" "CoefficientSupportedKZeroForgetComparison.lean:60"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedPerfectKEquiv_forget
attribute [colib_ref "quillen" "CoefficientSupportedKZeroForgetComparison.lean:74"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedBassBottomZeroIso_forget

end AlgebraicGeometry.Scheme.Modules

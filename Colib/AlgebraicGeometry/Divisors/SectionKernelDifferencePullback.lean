/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.SectionKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import Colib.Util.References

/-!
# Relative section-divisor differences under base change

For a separated smooth relative curve, the native section-kernel theorem supplies
Cartier divisors before and after arbitrary base change. The literal kernel equality
then gives a module isomorphism from the pulled-back divisor difference to the
base-changed sections' difference. In particular this applies to the closed fibre
over a strictly henselian local base; neither strict henselianity nor properness
is needed for this comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X S T : Scheme.{u}} (q : X ⟶ S) (g : T ⟶ S)
  [IsSeparated q] [SmoothOfRelativeDimension 1 q]

omit [SmoothOfRelativeDimension 1 q] in
/-- The image subscheme of a section is isomorphic to its base, with its full scheme structure. -/
theorem sectionKernelStructureMap_isIso (s : S ⟶ X) (hs : s ≫ q = 𝟙 S) :
    IsIso (s.ker.subschemeι ≫ q) := by
  have : IsClosedImmersion (s ≫ q) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
  have h : s.toImage ≫ (s.ker.subschemeι ≫ q) = 𝟙 _ := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hs]
  have heq : s.ker.subschemeι ≫ q = inv s.toImage := by
    apply (cancel_epi s.toImage).1
    simpa using h
  rw [heq]
  infer_instance

/-- A section of a separated smooth relative curve cuts out a Cartier divisor.
Its image is finite locally free of rank one over the base, so native Tag 0B9D applies. -/
@[stacks 0B9D "The finite locally free image of a section is a relative Cartier divisor"]
theorem isEffectiveCartierDivisor_sectionKernel (s : S ⟶ X) (hs : s ≫ q = 𝟙 S) :
    IsEffectiveCartierDivisor s.ker := by
  have := sectionKernelStructureMap_isIso q s hs
  have : Stacks.Morphisms.IsFiniteLocallyFree (s.ker.subschemeι ≫ q) :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact (AlgebraicGeometry.isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree q s.ker).1

/-- Arbitrary base change preserves the Cartier section-kernel divisor
of a smooth relative curve. -/
theorem isPullbackDefined_sectionKernel (s : S ⟶ X) (hs : s ≫ q = 𝟙 S) :
    IsPullbackDefined (pullback.fst q g) s.ker := by
  have : SmoothOfRelativeDimension 1 (pullback.snd q g) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback q g) inferInstance
  have h := isEffectiveCartierDivisor_sectionKernel (pullback.snd q g)
    (Scheme.baseChangedSection q g s hs) (Scheme.baseChangedSection_snd q g s hs)
  change IsEffectiveCartierDivisor _
  rwa [Scheme.ker_baseChangedSection] at h

/-- The actual module comparison for the signed difference of two section kernels.
The positive section remains first and the negative section remains second. -/
@[colib_tag "COL-1038", stacks 0C4U
  "Cartier sheaf pullback for actual base-changed section kernels"]
def sectionKernelDifferencePullbackIso
    (s t : S ⟶ X) (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S) :
    (Scheme.Modules.pullback (pullback.fst q g)).obj (differenceSheaf s.ker t.ker) ≅
      differenceSheaf (Scheme.baseChangedSection q g s hs).ker
        (Scheme.baseChangedSection q g t ht).ker := by
  have := isEffectiveCartierDivisor_sectionKernel q s hs
  have := isEffectiveCartierDivisor_sectionKernel q t ht
  have := isPullbackDefined_sectionKernel q g s hs
  have := isPullbackDefined_sectionKernel q g t ht
  exact differenceSheafPullbackIso (pullback.fst q g) s.ker t.ker ≪≫
    eqToIso (congrArg₂ differenceSheaf
      (Scheme.ker_baseChangedSection q g s hs).symm
      (Scheme.ker_baseChangedSection q g t ht).symm)

end Stacks.Divisors

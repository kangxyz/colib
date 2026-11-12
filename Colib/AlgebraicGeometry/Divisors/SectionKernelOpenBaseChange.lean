/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.SectionKernelCartesian
public import Colib.AlgebraicGeometry.Divisors.SectionKernelSmoothOpen

/-!
# Divisor differences of original sections in Cartesian curve families

Only the retained opens need to be smooth. The actual source and target sections,
not replacements on chosen pullback objects, give the signed module comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Divisors

/-- For specified Cartesian sections, Cartierness of the actual target kernel makes
pullback of the original kernel defined. The full ideal, not its reduction, is used. -/
theorem isPullbackDefined_sectionKernel_cartesian
    {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (q' : X' ⟶ S')
    (q : X ⟶ S) (g : S' ⟶ S) [IsSeparated q] (h : IsPullback f q' q g)
    (s' : S' ⟶ X') (s : S ⟶ X)
    (hs' : s' ≫ q' = 𝟙 S') (hs : s ≫ q = 𝟙 S)
    (hsec : s' ≫ f = g ≫ s) [IsEffectiveCartierDivisor s'.ker] :
    IsPullbackDefined f s.ker := by
  change IsEffectiveCartierDivisor (s.ker.comap f)
  rw [← Scheme.ker_section_of_isPullback f q' q g h s' s hs' hs hsec]
  infer_instance

/-- The signed difference comparison keeps both original sections in the supplied
Cartesian square. Smoothness is needed only on opens containing their images. -/
def sectionKernelDifferenceCartesianIso
    {X' X S' S U' U : Scheme.{u}} (f : X' ⟶ X) (q' : X' ⟶ S')
    (q : X ⟶ S) (g : S' ⟶ S) [IsSeparated q] (h : IsPullback f q' q g)
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (j' : U' ⟶ X') [IsOpenImmersion j'] [SmoothOfRelativeDimension 1 (j' ≫ q')]
    (s t : S ⟶ X) (s' t' : S' ⟶ X')
    (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S)
    (hs' : s' ≫ q' = 𝟙 S') (ht' : t' ≫ q' = 𝟙 S')
    (hsec : s' ≫ f = g ≫ s) (htec : t' ≫ f = g ≫ t)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j)
    (hsj' : Set.range s' ⊆ Set.range j') (htj' : Set.range t' ⊆ Set.range j') :
    (Scheme.Modules.pullback f).obj (differenceSheaf s.ker t.ker) ≅
      differenceSheaf s'.ker t'.ker := by
  have : IsSeparated q' := MorphismProperty.of_isPullback h inferInstance
  have := isEffectiveCartierDivisor_sectionKernel_of_range_subset q j s hs hsj
  have := isEffectiveCartierDivisor_sectionKernel_of_range_subset q j t ht htj
  have := isEffectiveCartierDivisor_sectionKernel_of_range_subset q' j' s' hs' hsj'
  have := isEffectiveCartierDivisor_sectionKernel_of_range_subset q' j' t' ht' htj'
  have := isPullbackDefined_sectionKernel_cartesian f q' q g h s' s hs' hs hsec
  have := isPullbackDefined_sectionKernel_cartesian f q' q g h t' t ht' ht htec
  exact differenceSheafPullbackIso f s.ker t.ker ≪≫
    eqToIso (congrArg₂ differenceSheaf
      (Scheme.ker_section_of_isPullback f q' q g h s' s hs' hs hsec).symm
      (Scheme.ker_section_of_isPullback f q' q g h t' t ht' ht htec).symm)

end Stacks.Divisors

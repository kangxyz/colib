/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.SectionKernelCartesian
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalBoundaryFramePullback

/-! # Actual section kernels on an original retained open

A factorization through an open immersion gives a Cartesian section square,
not a Cartesian square for the whole curve over the unchanged base.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme

/-- A specified factorization through an open immersion is the actual Cartesian
square of the closed section with that open immersion. -/
theorem isPullback_section_openRestriction {S X' X : Scheme.{u}}
    (f : X' ⟶ X) [IsOpenImmersion f] (s : S ⟶ X) (s' : S ⟶ X')
    (hs : s' ≫ f = s) : IsPullback s' (𝟙 S) f s :=
  IsPullback.of_vert_isIso_mono ⟨by simpa using hs⟩

/-- The original factored section has exactly the inverse image of the original
full kernel ideal, without a whole-curve Cartesian hypothesis. -/
theorem ker_section_openRestriction {S X' X : Scheme.{u}}
    (f : X' ⟶ X) [IsOpenImmersion f] (s : S ⟶ X) [IsClosedImmersion s]
    (s' : S ⟶ X') (hs : s' ≫ f = s) : s'.ker = s.ker.comap f :=
  ker_eq_comap_of_isPullback s' (𝟙 S) f s (isPullback_section_openRestriction f s s' hs)

end AlgebraicGeometry.Scheme
namespace Stacks.Divisors

/-- Cartierness of the actual restricted kernel proves that the original
Cartier pullback is defined. -/
theorem isPullbackDefined_sectionKernel_openRestriction {S X' X : Scheme.{u}}
    (f : X' ⟶ X) [IsOpenImmersion f] (s : S ⟶ X) [IsClosedImmersion s]
    (s' : S ⟶ X') (hs : s' ≫ f = s) [IsEffectiveCartierDivisor s'.ker] :
    IsPullbackDefined f s.ker := by
  change IsEffectiveCartierDivisor (s.ker.comap f)
  rw [← Scheme.ker_section_openRestriction f s s' hs]
  infer_instance

/-- The actual signed section difference comparison on a retained open. -/
def sectionKernelDifferenceOpenRestrictionIso {S X' X : Scheme.{u}}
    (f : X' ⟶ X) [IsOpenImmersion f]
    (s t : S ⟶ X) [IsClosedImmersion s] [IsClosedImmersion t]
    (s' t' : S ⟶ X') (hs : s' ≫ f = s) (ht : t' ≫ f = t)
    [IsEffectiveCartierDivisor s.ker] [IsEffectiveCartierDivisor t.ker]
    [IsEffectiveCartierDivisor s'.ker] [IsEffectiveCartierDivisor t'.ker] :
    (Scheme.Modules.pullback f).obj (differenceSheaf s.ker t.ker) ≅
      differenceSheaf s'.ker t'.ker := by
  let := isPullbackDefined_sectionKernel_openRestriction f s s' hs
  let := isPullbackDefined_sectionKernel_openRestriction f t t' ht
  exact differenceSheafPullbackIso f s.ker t.ker ≪≫
    eqToIso (congrArg₂ differenceSheaf
      (Scheme.ker_section_openRestriction f s s' hs).symm
      (Scheme.ker_section_openRestriction f t t' ht).symm)

/-- Canonical boundary frames respect literal equalities of the two full ideals. -/
theorem differenceSheafBoundaryIso_congr {B X : Scheme.{u}} (i : B ⟶ X)
    (D E D' E' : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    [IsEffectiveCartierDivisor D'] [IsEffectiveCartierDivisor E']
    (hD : D = D') (hE : E = E')
    (aD : ∀ y : B, i y ∉ D.support) (aE : ∀ y : B, i y ∉ E.support)
    (aD' : ∀ y : B, i y ∉ D'.support) (aE' : ∀ y : B, i y ∉ E'.support) :
    (Scheme.Modules.pullback i).mapIso (eqToIso (congrArg₂ differenceSheaf hD hE)) ≪≫
      differenceSheafBoundaryIso i D' E' aD' aE' =
      differenceSheafBoundaryIso i D E aD aE := by
  subst D'
  subst E'
  simp

/-- The original boundary avoids the actual factored section kernel. -/
theorem avoids_sectionKernel_openRestriction {S B' B X' X : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X') (f : X' ⟶ X)
    [IsOpenImmersion f] (w : b ≫ i = i' ≫ f)
    (s : S ⟶ X) [IsClosedImmersion s] (s' : S ⟶ X') (hs : s' ≫ f = s)
    (a : ∀ y : B, i y ∉ s.ker.support) : ∀ y : B', i' y ∉ s'.ker.support := by
  rw [Scheme.ker_section_openRestriction f s s' hs]
  exact avoids_support_comap_square b i i' f w s.ker a

/-- The precise section-kernel comparison preserves the original canonical frame
on the full boundary, including transport through the actual kernel equalities. -/
theorem sectionKernelDifferenceOpenRestrictionIso_boundary {S B' B X' X : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ X) (i' : B' ⟶ X') (f : X' ⟶ X)
    [IsOpenImmersion f] (w : b ≫ i = i' ≫ f)
    (s t : S ⟶ X) [IsClosedImmersion s] [IsClosedImmersion t]
    (s' t' : S ⟶ X') (hs : s' ≫ f = s) (ht : t' ≫ f = t)
    [IsEffectiveCartierDivisor s.ker] [IsEffectiveCartierDivisor t.ker]
    [IsEffectiveCartierDivisor s'.ker] [IsEffectiveCartierDivisor t'.ker]
    (aD : ∀ y : B, i y ∉ s.ker.support) (aE : ∀ y : B, i y ∉ t.ker.support) :
    (Scheme.Modules.pullback i').mapIso
      (sectionKernelDifferenceOpenRestrictionIso f s t s' t' hs ht) ≪≫
      differenceSheafBoundaryIso i' s'.ker t'.ker
        (avoids_sectionKernel_openRestriction b i i' f w s s' hs aD)
        (avoids_sectionKernel_openRestriction b i i' f w t t' ht aE) =
    pullbackBoundaryTrivialization b i i' f w (differenceSheaf s.ker t.ker)
      (differenceSheafBoundaryIso i s.ker t.ker aD aE) := by
  let := isPullbackDefined_sectionKernel_openRestriction f s s' hs
  let := isPullbackDefined_sectionKernel_openRestriction f t t' ht
  rw [sectionKernelDifferenceOpenRestrictionIso, Functor.mapIso_trans, Iso.trans_assoc]
  rw [differenceSheafBoundaryIso_congr i' (s.ker.comap f) (t.ker.comap f) s'.ker t'.ker
    (Scheme.ker_section_openRestriction f s s' hs).symm
    (Scheme.ker_section_openRestriction f t t' ht).symm
    (avoids_support_comap_square b i i' f w s.ker aD)
    (avoids_support_comap_square b i i' f w t.ker aE)]
  exact differenceSheafBoundaryIso_pullback_square b i i' f w s.ker t.ker aD aE

end Stacks.Divisors

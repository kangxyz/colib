/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.SectionKernelSmoothOpen
public import Colib.AlgebraicGeometry.Divisors.DifferenceSheafBoundary

/-!
# The difference of sections with the same specialization

The actual kernel divisors are pulled back along the chosen base change. Equality
of the two specialized morphisms gives equality of their literal kernel ideals;
the native dual-evaluation pairing then trivializes their difference. Smoothness
is needed only on an open containing the two original section images.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Equality of the specialized original morphisms implies equality of the actual
pullback-lift sections, rather than just equality of their underlying points. -/
theorem baseChangedSection_eq_of_comp_eq {X S T : Scheme.{u}}
    (q : X ⟶ S) (g : T ⟶ S) (s t : S ⟶ X)
    (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S) (hst : g ≫ s = g ≫ t) :
    baseChangedSection q g s hs = baseChangedSection q g t ht := by
  apply pullback.hom_ext <;> simp [hst]

end AlgebraicGeometry.Scheme

namespace Stacks.Divisors

/-- Cancellation of the same Cartier divisor is the native evaluation pairing
`𝒪(D) ⊗ 𝒪(-D) → 𝒪`, not an abstract equality of Picard classes. -/
@[colib_tag "COL-1054", stacks 01CT
  "The native dual evaluation trivializes the difference of the same Cartier divisor"]
def differenceSheafSelfIso {X : Scheme.{u}} (D : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D] :
    differenceSheaf D D ≅ SheafOfModules.unit X.ringCatSheaf := by
  letI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (negativeTwist' D) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hD
  exact Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' D)

/-- Pullback of the signed difference preserves the original section maps and signs.
The ambient morphism need not be smooth. -/
@[colib_tag "COL-1054", stacks 0C4U
  "Pullback of the literal section-kernel difference when smoothness is confined to an open"]
def sectionKernelDifferencePullbackIso_of_range_subset
    {X U S T : Scheme.{u}} (q : X ⟶ S) [IsSeparated q] (g : T ⟶ S)
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s t : S ⟶ X) (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j) :
    (Scheme.Modules.pullback (pullback.fst q g)).obj (differenceSheaf s.ker t.ker) ≅
      differenceSheaf (Scheme.baseChangedSection q g s hs).ker
        (Scheme.baseChangedSection q g t ht).ker := by
  have := isEffectiveCartierDivisor_sectionKernel_of_range_subset q j s hs hsj
  have := isEffectiveCartierDivisor_sectionKernel_of_range_subset q j t ht htj
  have := isPullbackDefined_sectionKernel_of_range_subset q g j s hs hsj
  have := isPullbackDefined_sectionKernel_of_range_subset q g j t ht htj
  exact differenceSheafPullbackIso (pullback.fst q g) s.ker t.ker ≪≫
    eqToIso (congrArg₂ differenceSheaf
      (Scheme.ker_baseChangedSection q g s hs).symm
      (Scheme.ker_baseChangedSection q g t ht).symm)

/-- Two sections with the same specialized morphism have a canonically trivial
specialized difference, using their actual pulled-back kernels and evaluation. -/
@[colib_tag "COL-1054"]
def sectionKernelDifferencePullbackUnitIso_of_range_subset
    {X U S T : Scheme.{u}} (q : X ⟶ S) [IsSeparated q] (g : T ⟶ S)
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s t : S ⟶ X) (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j)
    (hst : g ≫ s = g ≫ t) :
    (Scheme.Modules.pullback (pullback.fst q g)).obj (differenceSheaf s.ker t.ker) ≅
      SheafOfModules.unit (pullback q g).ringCatSheaf := by
  have := isEffectiveCartierDivisor_baseChangedSection_of_range_subset q g j s hs hsj
  have hker : (Scheme.baseChangedSection q g t ht).ker =
      (Scheme.baseChangedSection q g s hs).ker :=
    congrArg Scheme.Hom.ker (Scheme.baseChangedSection_eq_of_comp_eq q g s t hs ht hst).symm
  let e : differenceSheaf (Scheme.baseChangedSection q g s hs).ker
      (Scheme.baseChangedSection q g t ht).ker ≅
        differenceSheaf (Scheme.baseChangedSection q g s hs).ker
          (Scheme.baseChangedSection q g s hs).ker :=
    eqToIso (congrArg (differenceSheaf (Scheme.baseChangedSection q g s hs).ker) hker)
  exact sectionKernelDifferencePullbackIso_of_range_subset q g j s t hs ht hsj htj ≪≫
    e ≪≫ differenceSheafSelfIso (Scheme.baseChangedSection q g s hs).ker

/-- The specified boundary frame depends on the actual section kernels on the full
ambient scheme and the full boundary, with no smoothness assumption on either. -/
@[colib_tag "COL-1054"]
def sectionKernelDifferenceBoundaryIso_of_range_subset
    {X U S B : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s t : S ⟶ X) (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j)
    (i : B ⟶ X) (his : Disjoint (Set.range i) (Set.range s))
    (hit : Disjoint (Set.range i) (Set.range t)) :
    (Scheme.Modules.pullback i).obj (differenceSheaf s.ker t.ker) ≅
      SheafOfModules.unit B.ringCatSheaf := by
  have : IsClosedImmersion (s ≫ q) := by rw [hs]; infer_instance
  have : IsClosedImmersion (t ≫ q) := by rw [ht]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t q
  have := isEffectiveCartierDivisor_sectionKernel_of_range_subset q j s hs hsj
  have := isEffectiveCartierDivisor_sectionKernel_of_range_subset q j t ht htj
  exact differenceSheafBoundaryIsoOfDisjointRange i s t his hit

end Stacks.Divisors

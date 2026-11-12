/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.SectionKernelDifferencePullback
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.BoundaryFiniteFlat

/-!
# Section divisors supported in a smooth curve open

The ambient separated scheme need not be smooth. A section whose image lies in
an open smooth relative curve has a Cartier kernel on the entire ambient scheme.
Arbitrary base change preserves this assertion and the original kernel ideals.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Divisors

/-- Restricting a closed section to an open through which it factors preserves its
literal kernel ideal. The comparison square uses the identity on the section's source. -/
theorem sectionKernel_comap_open {X U S : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (s : S ⟶ X) [IsClosedImmersion s]
    (sU : S ⟶ U) (hsU : sU ≫ j = s) : s.ker.comap j = sU.ker := by
  have h : IsPullback sU (𝟙 S) j s :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hsU⟩
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- Smoothness is needed only on an open containing the image of the original section.
The conclusion concerns its kernel on the whole separated ambient scheme. -/
@[colib_tag "COL-1054", stacks 0B9D
  "A Cartier section divisor in a smooth curve open extends over the whole scheme"]
theorem isEffectiveCartierDivisor_sectionKernel_of_range_subset
    {X U S : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s : S ⟶ X) (hs : s ≫ q = 𝟙 S) (h : Set.range s ⊆ Set.range j) :
    IsEffectiveCartierDivisor s.ker := by
  have : IsClosedImmersion (s ≫ q) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
  let sU := IsOpenImmersion.lift j s h
  have hsU : sU ≫ j = s := IsOpenImmersion.lift_fac j s h
  have hsUq : sU ≫ (j ≫ q) = 𝟙 S := by rw [← Category.assoc, hsU, hs]
  have hcart := isEffectiveCartierDivisor_sectionKernel (j ≫ q) sU hsUq
  apply isEffectiveCartierDivisor_of_comap_of_range_subset j s.ker
  · rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
      s.isClosedEmbedding.isClosed_range.closure_eq]
    exact h
  · rwa [sectionKernel_comap_open j s sU hsU]

/-- The original smooth open after the same base change as the ambient scheme. -/
def baseChangedOpen {X U S T : Scheme.{u}} (q : X ⟶ S) (g : T ⟶ S)
    (j : U ⟶ X) : pullback (j ≫ q) g ⟶ pullback q g :=
  pullback.map (j ≫ q) g q g j (𝟙 T) (𝟙 S) (by simp) (by simp)

/-- The original section's base change still lies in the actual base-changed open. -/
theorem range_baseChangedSection_subset_baseChangedOpen
    {X U S T : Scheme.{u}} (q : X ⟶ S) (g : T ⟶ S)
    (j : U ⟶ X) [IsOpenImmersion j]
    (s : S ⟶ X) (hs : s ≫ q = 𝟙 S) (h : Set.range s ⊆ Set.range j) :
    Set.range (Scheme.baseChangedSection q g s hs) ⊆ Set.range (baseChangedOpen q g j) := by
  let sU := IsOpenImmersion.lift j s h
  have hsU : sU ≫ j = s := IsOpenImmersion.lift_fac j s h
  have hsUq : sU ≫ (j ≫ q) = 𝟙 S := by rw [← Category.assoc, hsU, hs]
  have heq : Scheme.baseChangedSection (j ≫ q) g sU hsUq ≫ baseChangedOpen q g j =
      Scheme.baseChangedSection q g s hs := by
    apply pullback.hom_ext
    · simp [baseChangedOpen, Category.assoc, ← hsU]
    · simp [baseChangedOpen]
  rintro _ ⟨x, rfl⟩
  exact ⟨Scheme.baseChangedSection (j ≫ q) g sU hsUq x,
    congrArg (fun f : T ⟶ pullback q g => f x) heq⟩

/-- A section supported in a smooth relative-curve open remains Cartier after arbitrary
base change, without smoothness or flatness of the entire ambient scheme. -/
@[colib_tag "COL-1054"]
theorem isEffectiveCartierDivisor_baseChangedSection_of_range_subset
    {X U S T : Scheme.{u}} (q : X ⟶ S) [IsSeparated q] (g : T ⟶ S)
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s : S ⟶ X) (hs : s ≫ q = 𝟙 S) (h : Set.range s ⊆ Set.range j) :
    IsEffectiveCartierDivisor (Scheme.baseChangedSection q g s hs).ker := by
  have : IsOpenImmersion (baseChangedOpen q g j) := by
    dsimp [baseChangedOpen]
    infer_instance
  have : SmoothOfRelativeDimension 1 (baseChangedOpen q g j ≫ pullback.snd q g) := by
    simpa [baseChangedOpen] using
      (inferInstance : SmoothOfRelativeDimension 1 (pullback.snd (j ≫ q) g))
  exact isEffectiveCartierDivisor_sectionKernel_of_range_subset (pullback.snd q g)
    (baseChangedOpen q g j) (Scheme.baseChangedSection q g s hs)
    (Scheme.baseChangedSection_snd q g s hs)
    (range_baseChangedSection_subset_baseChangedOpen q g j s hs h)

/-- Pullback is defined on the literal original section kernel. -/
theorem isPullbackDefined_sectionKernel_of_range_subset
    {X U S T : Scheme.{u}} (q : X ⟶ S) [IsSeparated q] (g : T ⟶ S)
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s : S ⟶ X) (hs : s ≫ q = 𝟙 S) (h : Set.range s ⊆ Set.range j) :
    IsPullbackDefined (pullback.fst q g) s.ker := by
  have hc := isEffectiveCartierDivisor_baseChangedSection_of_range_subset q g j s hs h
  change IsEffectiveCartierDivisor _
  rwa [Scheme.ker_baseChangedSection] at hc

end Stacks.Divisors

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.CompatibleBoundaryFrames
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalSection

/-!
# Nonzero sections from the actual compatible geometric pair

COL-1048 constructs the whole Cartier, finite locally free zero schemes and compatible
full-boundary frames. Their original sections are nonzero on an integral compactification:
Cartier regularity gives native regular sections, hence nonzero global values. This argument
does not assume the boundary is nonempty or reduced. The denominator is presented through the
native equivalence with global sections, retaining the same value and the same zero scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.ProjectiveCohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry

/-- The original global value is nonzero when its whole zero scheme is Cartier. -/
theorem globalSection_ne_zero_of_isEffectiveCartierDivisor_zeroScheme
    {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X L s)) :
    s ≠ 0 := by
  let t : L.sections := (Stacks.NonvanishingSpelling.sectionsEquiv X L).symm s
  have ht : t.eval (op ⊤) = s :=
    (Stacks.NonvanishingSpelling.sectionsEquiv X L).apply_symm_apply s
  have hreg := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L t).mp
    (ht.symm ▸ hs)
  exact ht ▸ globalSection_ne_zero_of_isRegularSection L t hreg

namespace Scheme.Modules

/-- A prescribed original boundary frame produces nonzero actual numerator and denominator,
with whole Cartier, finite locally free zero schemes supported in the retained smooth open. -/
@[colib_tag "COL-1079", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/PicardUFD/Affine.lean:102-125"
  "ingredient" "Affine invertible-sheaf triviality in the auxiliary full-boundary frame \
    supplier; the nonzero pair is assembled here."]
theorem exists_nonzero_compatible_boundary_framed_divisor_pair
    (R B : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] (n : ℕ)
    {X U V : Scheme.{u}} [IsIntegral X] [IsAffine V] [U.IsQuasiAffine]
    (g : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion g]
    (q : X ⟶ V) [IsProper q] (i : Spec (CommRingCat.of B) ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (M : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (e : (pullback i).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :
    ∃ C : ℤ, ∀ d : ℤ, C ≤ d →
      let H := (pullback g).obj (twistingSheaf (polyGrading R n) d)
      ∃ eH : (pullback i).obj H ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf,
      ∃ (a : Γ((pullbackTwistFunctor R n g d).obj M, ⊤)) (b : H.sections),
        a ≠ 0 ∧ b.eval (op ⊤) ≠ 0 ∧
        Hom.app (pullbackTensorFrame i M H e eH).hom ⊤ (pullbackGlobalSections i _ a) =
          (1 : Γ(Spec (CommRingCat.of B), ⊤)) ∧
        Hom.app eH.hom ⊤ (pullbackGlobalSections i H (b.eval (op ⊤))) =
          (1 : Γ(Spec (CommRingCat.of B), ⊤)) ∧
        Stacks.Divisors.IsRelativeEffectiveCartierDivisor q
          (zeroScheme X ((pullbackTwistFunctor R n g d).obj M) a) ∧
        Stacks.Morphisms.IsFiniteLocallyFree
          ((zeroScheme X ((pullbackTwistFunctor R n g d).obj M) a).subschemeι ≫ q) ∧
        Set.range (zeroScheme X ((pullbackTwistFunctor R n g d).obj M) a).subschemeι ⊆
          Set.range j ∧
        Stacks.Divisors.IsRelativeEffectiveCartierDivisor q
          (zeroScheme X H (b.eval (op ⊤))) ∧
        Stacks.Morphisms.IsFiniteLocallyFree ((zeroScheme X H (b.eval (op ⊤))).subschemeι ≫ q) ∧
        Set.range (zeroScheme X H (b.eval (op ⊤))).subschemeι ⊆ Set.range j := by
  obtain ⟨C, hC⟩ := exists_compatible_boundary_framed_divisor_pair R B n g q i j hcover M e
  refine ⟨C, fun d hd => ?_⟩
  let H := (pullback g).obj (twistingSheaf (polyGrading R n) d)
  obtain ⟨eH, a, b, haB, hbB, hA, hAfin, hAU, hB, hBfin, hBU⟩ := hC d hd
  let bS : H.sections := (Stacks.NonvanishingSpelling.sectionsEquiv X H).symm b
  have hbS : bS.eval (op ⊤) = b :=
    (Stacks.NonvanishingSpelling.sectionsEquiv X H).apply_symm_apply b
  refine ⟨eH, a, bS, ?_, ?_, haB, ?_, hA, hAfin, hAU, ?_, ?_, ?_⟩
  · exact globalSection_ne_zero_of_isEffectiveCartierDivisor_zeroScheme _ a hA.1
  · rw [hbS]
    exact globalSection_ne_zero_of_isEffectiveCartierDivisor_zeroScheme H b hB.1
  · simpa only [hbS] using hbB
  · simpa only [hbS] using hB
  · exact (congrArg (fun z : Γ(H, ⊤) => Stacks.Morphisms.IsFiniteLocallyFree
      ((zeroScheme X H z).subschemeι ≫ q)) hbS).mpr hBfin
  · exact (congrArg (fun z : Γ(H, ⊤) =>
      Set.range (zeroScheme X H z).subschemeι ⊆ Set.range j) hbS).mpr hBU

end Scheme.Modules

end AlgebraicGeometry

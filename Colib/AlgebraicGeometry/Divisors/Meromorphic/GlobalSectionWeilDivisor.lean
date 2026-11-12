/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalSection
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CommonNonvanishingRatioGeneric
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral

/-!
# The original global section and its full Cartier zero divisor

The actual zero scheme is Cartier by the native regular-section theorem. Its native Weil
divisor has the same full local lengths as the original meromorphic section, without reduction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X]

/-- A nonzero global section is nonvanishing at the original generic point, in the native
nonvanishing-open spelling used by tensor division. -/
theorem genericPoint_mem_nonvanishingOpen_of_eval_top_ne_zero (L : X.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
    (b : L.sections) (hb : b.eval (op (⊤ : X.Opens)) ≠ 0) :
    genericPoint X ∈ Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) L b := by
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    hL.toAlgebraicGeometry
  have : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L
  have h := genericPoint_mem_localNonvanishing_of_regularMeromorphic L ⊤ trivial
    (b.eval (op ⊤)) (meromorphicSectionOfGlobalSection L (b.eval (op ⊤)))
    (isRegularMeromorphicSection_meromorphicSectionOfGlobalSection L _ hb)
    (meromorphicGenericValue_meromorphicSectionOfGlobalSection L _)
  change genericPoint X ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L b
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq]
  exact h.2

/-- The original nonzero global section's actual zero scheme is the literal native Weil
divisor of its meromorphic image. The Cartier proof is produced, not assumed. -/
@[colib_tag "COL-1066",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/RegularSectionIntegral.lean:171-184"
    "ingredient" "The original nonzero global section produces its actual Cartier zero scheme"]
theorem weilDivisorOfMeromorphicSection_globalSection_eq_zeroScheme [IsNoetherian X]
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    weilDivisorOfMeromorphicSection X L (meromorphicSectionOfGlobalSection L s)
        (isRegularMeromorphicSection_meromorphicSectionOfGlobalSection L s hs) =
      effectiveCartierWeilDivisor (Stacks.Divisors.zeroScheme X L s)
        (isEffectiveCartierDivisor_zeroScheme_of_ne_zero L s hs) := by
  apply Subtype.ext
  funext Z
  exact orderOfVanishingMeromorphic_globalSection_eq_length L s hs Z

end AlgebraicGeometry

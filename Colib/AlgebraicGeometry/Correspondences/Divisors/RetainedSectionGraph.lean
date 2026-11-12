/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Divisors.RetainedFiniteFlat
public import Colib.AlgebraicGeometry.Correspondences.Divisors.SectionKernel
public import Colib.AlgebraicGeometry.Divisors.SectionKernelSmoothOpen

/-!
# Original section graphs after retaining the smooth open

The original compactified section factors through the actual open. Its literal kernel pulls
back to the kernel of that same factor, whose whole image scheme projects isomorphically to
the original source. Thus the retained whole divisor correspondence is exactly the native
graph with the original target map. Only reducedness of the source is used for graph weights.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {C U V Y S : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsReduced V]
  (p : V ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t]
  (q : C ⟶ V) [IsSeparated q] (j : U ⟶ C) [IsOpenImmersion j]
  (r : U ⟶ pullback p t) (hr : r ≫ pullback.fst p t = j ≫ q)
  (s : V ⟶ C) (hs : s ≫ q = 𝟙 V) (sU : V ⟶ U) (hsU : sU ≫ j = s)
  (hI : Set.range s.ker.subschemeι ⊆ Set.range j)
  [Stacks.Morphisms.IsFiniteLocallyFree (s.ker.subschemeι ≫ q)]

include hr hs hsU in
omit [AlgebraicGeometry.IsNoetherian U] [AlgebraicGeometry.IsNoetherian V] [IsReduced V]
  [IsSeparated t] [LocallyOfFiniteType t] [IsSeparated q] [IsOpenImmersion j]
  [Stacks.Morphisms.IsFiniteLocallyFree (s.ker.subschemeι ≫ q)] in
/-- The unchanged section of the retained open remains a section of the original first map. -/
theorem retainedSection_firstProjection : sU ≫ (r ≫ pullback.fst p t) = 𝟙 V := by
  rw [hr, ← Category.assoc, hsU, hs]

/-- The native retained whole section divisor is the original graph, with no reduction of its
scheme or replacement of its source-target map. -/
@[colib_tag "COL-1072"]
theorem retainedFiniteFlatDivisorCorrespondence_sectionKernel :
    retainedFiniteFlatDivisorCorrespondence p t q j r hr s.ker hI =
      graphCorrespondenceOfComponents p t (sU ≫ r ≫ pullback.snd p t)
        (sectionTarget_base p t r sU (retainedSection_firstProjection p t q j r hr s hs sU hsU))
        (AlgebraicCycle.fundamentalCycle_genericPoints_finite V) := by
  have : IsClosedImmersion (s ≫ q) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
  have : IsSeparated (r ≫ pullback.fst p t) := by rw [hr]; infer_instance
  have hsec := retainedSection_firstProjection p t q j r hr s hs sU hsU
  have := retainedDivisor_firstProjection_finiteLocallyFree p t q j r hr s.ker hI
  have := Stacks.Morphisms.IsFiniteLocallyFree.isFinite
    (((s.ker.comap j).subschemeι ≫ r) ≫ pullback.fst p t)
  have := Stacks.Morphisms.IsFiniteLocallyFree.flat
    (((s.ker.comap j).subschemeι ≫ r) ≫ pullback.fst p t)
  change finiteFlatDivisorCorrespondence p t r (s.ker.comap j) = _
  have hker := Stacks.Divisors.sectionKernel_comap_open j s sU hsU
  have := sectionKernelProjection_isIso p t r sU hsec
  convert finiteFlatDivisorCorrespondence_sectionKernel p t r sU hsec using 1
  congr 1

end Stacks.Chow

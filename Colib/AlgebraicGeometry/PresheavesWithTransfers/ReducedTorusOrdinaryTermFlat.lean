/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusTermFlat
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Flat terms of the original ordinary reduced-torus complex

These statements concern the actual alternating complex and its native extension,
not a replacement resolution. They do not yet assert categorical K-flatness.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicTopology AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The original alternating chains, before any localization or sheafification. -/
abbrev reducedTorusOrdinaryIntegralChains (q : ℕ) :=
  (alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q)

/-- Alternating chains retain the actual simplex sections as their terms. -/
instance reducedTorusOrdinaryIntegralChains_sections_flat (q n : ℕ)
    (X : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ) :
    Module.Flat ℤ (((reducedTorusOrdinaryIntegralChains k q).X n).obj X) :=
  reducedTorusIntSimplicial_sections_flat k q (op (SimplexCategory.mk n)) X

/-- The native nonpositive extension used by the ordinary localized roof. -/
abbrev reducedTorusOrdinaryIntegralCochains (q : ℕ) :=
  (reducedTorusOrdinaryIntegralChains k q).extend ComplexShape.embeddingDownNat

/-- The upper bound is supplied by the native extension, without truncating the input. -/
instance reducedTorusOrdinaryIntegralCochains_isStrictlyLE (q : ℕ) :
    CochainComplex.IsStrictlyLE (reducedTorusOrdinaryIntegralCochains k q) 0 := inferInstance

/-- Every retained term is flat on the original smooth-site sections. -/
instance reducedTorusOrdinaryIntegralCochains_sections_flat_neg (q n : ℕ)
    (X : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ) :
    Module.Flat ℤ (((reducedTorusOrdinaryIntegralCochains k q).X (-(n : ℤ))).obj X) := by
  let e := (Functor.mapIso ((CategoryTheory.evaluation _ _).obj X)
    ((reducedTorusOrdinaryIntegralChains k q).extendXIso
      ComplexShape.embeddingDownNat (i := n) rfl))
  let : Module.Flat ℤ
      ((((CategoryTheory.evaluation _ (ModuleCat ℤ)).obj X).obj
        ((reducedTorusOrdinaryIntegralChains k q).X n))) :=
    reducedTorusOrdinaryIntegralChains_sections_flat k q n X
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- The remaining degrees are genuinely zero, not unspecified additional terms. -/
theorem reducedTorusOrdinaryIntegralCochains_isZero_X (q : ℕ) (n : ℤ) (hn : 0 < n) :
    Limits.IsZero ((reducedTorusOrdinaryIntegralCochains k q).X n) :=
  CochainComplex.isZero_of_isStrictlyLE _ 0 n hn

end AlgebraicGeometry.PresheafWithTransfers

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Kernel ideals in a specified Cartesian square

This common lower interface is extracted from the strict A¹ marked-graph geometry
at commit `6fac947`. Both marked graphs and section families retain their existing
public names as wrappers around this single native ideal-sheaf proof.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A specified pullback of a closed immersion retains its full kernel ideal. -/
theorem ker_eq_comap_of_isPullback
    {Z' Z X' X : Scheme.{u}} (i' : Z' ⟶ X') (g : Z' ⟶ Z)
    (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    (h : IsPullback i' g f i) : i'.ker = i.ker.comap f := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

end AlgebraicGeometry.Scheme.Hom

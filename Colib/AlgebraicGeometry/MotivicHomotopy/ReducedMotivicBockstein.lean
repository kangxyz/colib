/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Complex
public import Colib.CategoryTheory.Sites.Simplicial.ReducedBockstein

/-!
# The mod-n Bockstein on reduced motivic cohomology

The reduced derived Hom functor uses the ordinary motivic sheaf complex
and its actual multiplication cone. Its Bockstein acts by the positive
connecting map followed by integral reduction in the next degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Cₖ" => SmoothSite (Spec (CommRingCat.of k))
local notation "Jₖ" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))

variable [HasDerivedCategory.{d}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Reduced hypercohomology of the original ordinary motivic coefficient cone. -/
abbrev reducedMotivicFiniteCohomology (q n : ℕ) (p : ℤ) :
    (PointedSimplicialPresheaf.{u + 1} Cₖ)ᵒᵖ ⥤ AddCommGrpCat.{d} :=
  reducedHypercohomology Cₖ Jₖ (motivicFiniteSheafComplex k q n) p

/-- The mod-`n` operation on the existing reduced motivic coefficient cone. -/
def reducedMotivicModBockstein (q n : ℕ) (p : ℤ) :
    reducedMotivicFiniteCohomology k q n p ⟶
      reducedMotivicFiniteCohomology k q n (p + 1) :=
  reducedModBockstein Cₖ Jₖ (motivicSheafComplex k q) n p

/-- Two consecutive reduced motivic Bocksteins compose to zero. -/
theorem reducedMotivicModBockstein_comp_eq_zero (q n : ℕ) (p : ℤ) :
    reducedMotivicModBockstein k q n p ≫ reducedMotivicModBockstein k q n (p + 1) = 0 :=
  reducedModBockstein_comp_eq_zero Cₖ Jₖ (motivicSheafComplex k q) n p

attribute [colib_tag "COL-1019"]
  reducedMotivicModBockstein
  reducedMotivicModBockstein_comp_eq_zero

end AlgebraicGeometry.MotivicHomotopy

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Complex
public import Colib.CategoryTheory.Sites.Simplicial.ReducedBockstein

/-!
# Reduced hypercohomology of the finite motivic coefficient complex

The original pointed simplicial presheaves on the smooth site take values in
simplicial sets in the field universe. Their reduced hypercohomology with the
actual finite coefficient complex has the natural cone Bockstein.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe d u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]
  [HasDerivedCategory.{d}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u})]

/-- Finite coefficient reduced hypercohomology on the original smooth pointed presheaves. -/
abbrev reducedMotivicFiniteCohomology (q n : ℕ) (p : ℤ) :
    (PointedSimplicialPresheaf.{u} (SmoothSite (Spec (.of k))))ᵒᵖ ⥤ AddCommGrpCat.{d} :=
  reducedHypercohomology (SmoothSite (Spec (.of k)))
    (SmoothSite.nisnevichTopology (Spec (.of k))) (motivicFiniteComplex k q n) p

/-- The mod-`n` Bockstein of the actual finite motivic coefficient complex. -/
def reducedMotivicModBockstein (q n : ℕ) (p : ℤ) :
    reducedMotivicFiniteCohomology k q n p ⟶ reducedMotivicFiniteCohomology k q n (p + 1) :=
  reducedModBockstein (SmoothSite (Spec (.of k)))
    (SmoothSite.nisnevichTopology (Spec (.of k))) (motivicComplex k q) n p

/-- The specialized Bocksteins in consecutive degrees compose to zero. -/
theorem reducedMotivicModBockstein_comp_eq_zero (q n : ℕ) (p : ℤ) :
    reducedMotivicModBockstein k q n p ≫ reducedMotivicModBockstein k q n (p + 1) = 0 :=
  reducedModBockstein_comp_eq_zero (SmoothSite (Spec (.of k)))
    (SmoothSite.nisnevichTopology (Spec (.of k))) (motivicComplex k q) n p

end AlgebraicGeometry

attribute [colib_tag "COL-0393"]
  AlgebraicGeometry.reducedMotivicFiniteCohomology
  AlgebraicGeometry.reducedMotivicModBockstein
  AlgebraicGeometry.reducedMotivicModBockstein_comp_eq_zero

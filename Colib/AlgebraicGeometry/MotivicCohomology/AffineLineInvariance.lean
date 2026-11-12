/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.HypercohomologyInvariance
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
import Colib.AlgebraicGeometry.Sites.Smooth.FiniteKrullDimension
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteCohomologicalDimension
import Colib.Util.References

/-!
# A¹-invariance of integral motivic cohomology

The smooth scheme and its affine-line cylinder each have a finite Krull
dimension bound. Their maximum bounds the projective dimensions of both
free Nisnevich representing sheaves. The finite hypercohomology window and
strict A¹-invariance of the motivic cohomology sheaves then give invariance
under the actual affine-line projection over a perfect field.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Cohomology.FreeYonedaUnivLE

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open SmoothSite.Contraction

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The actual integral motivic cohomology presheaf is A¹-invariant
over a perfect field in every integer degree and nonnegative weight. -/
@[colib_tag "COL-1033", colib_ref "MVW2006" "Lecture 14, Proposition 14.8, forward direction"
  "adaptation" "Ordinary hypercohomology of the integral motivic coefficient complex"]
theorem motivicCohomologyPresheaf_isA1Invariant (p : ℤ) (q : ℕ) :
    A1.IsInvariant (.of k) (motivicCohomologyPresheaf k p q) := by
  intro X
  let X₁ := (affineLineCylinder (S := Spec (.of k))).obj X
  obtain ⟨dX, hX⟩ := SmoothSite.exists_nat_topologicalKrullDim_le k X
  obtain ⟨d₁, h₁⟩ := SmoothSite.exists_nat_topologicalKrullDim_le k X₁
  let d := max dX d₁
  have hdX : (dX : WithBot ℕ∞) ≤ d :=
    WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (le_max_left dX d₁))
  have hd₁ : (d₁ : WithBot ℕ∞) ≤ d :=
    WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (le_max_right dX d₁))
  have hDimX := SmoothSite.freeYoneda_hasProjectiveDimensionLE_of_krullDim_le X d
    (hX.trans hdX)
  have hDim₁ := SmoothSite.freeYoneda_hasProjectiveDimensionLE_of_krullDim_le X₁ d
    (h₁.trans hd₁)
  exact isIso_motivicCohomologyRestriction_affineLineProjection k p q X d
    (hX := hDimX) (hCylinder := hDim₁)

end AlgebraicGeometry.PresheafWithTransfers

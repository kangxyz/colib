/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.OrdinaryComparison
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Colib.AlgebraicGeometry.Sites.Smooth.FiniteKrullDimension
import Colib.AlgebraicGeometry.Sites.Smooth.Injectives
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteCohomologicalDimension

/-!
# Finite projective dimension of the actual transfer representable

The original comparison with ordinary Nisnevich cohomology transports
the dimension bound to the transfer representable of a smooth scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]

/-- The actual transfer representable satisfies the Nisnevich dimension bound. -/
theorem transferRepresentable_hasProjectiveDimensionLE_of_krullDim_le
    (X : SmoothSite (Spec (.of k))) (d : ℕ) (hX : topologicalKrullDim X.left ≤ d) :
    HasProjectiveDimensionLE ((transferRepresentable k).obj (Cor.mk X)) d := by
  let : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) := hasExt_of_enoughInjectives _
  let : HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
    letI := SmoothSite.sheaf_enoughInjectives (Spec (.of k))
    hasExt_of_enoughInjectives _
  refine HasProjectiveDimensionLT.mk ?_
  intro n hn F e
  have hdn : (d : WithBot ℕ∞) < n :=
    WithBot.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Nat.lt_of_succ_le hn))
  apply (transferExtEquiv k X F n).injective
  rw [map_zero]
  exact SmoothSite.nisnevichCohomology_eq_zero_of_krullDim_lt
    ((toSheaf k).obj F) n X (hX.trans_lt hdn) _

/-- Every smooth transfer representable has a finite projective dimension bound. -/
theorem exists_transferRepresentable_hasProjectiveDimensionLE
    (X : SmoothSite (Spec (.of k))) :
    ∃ d : ℕ, HasProjectiveDimensionLE ((transferRepresentable k).obj (Cor.mk X)) d := by
  obtain ⟨d, hd⟩ := SmoothSite.exists_nat_topologicalKrullDim_le k X
  exact ⟨d, transferRepresentable_hasProjectiveDimensionLE_of_krullDim_le k X d hd⟩

end AlgebraicGeometry.SheafWithTransfers

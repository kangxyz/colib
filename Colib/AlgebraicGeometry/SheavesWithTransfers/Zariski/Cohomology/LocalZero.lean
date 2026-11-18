/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.PerfectField
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Sheafification.LocalZero
public import Colib.AlgebraicGeometry.Sites.Smooth.Injectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.TransferInvariance
import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen

/-! # Zariski-local vanishing of positive Nisnevich cohomology -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] [PerfectField k]

local notation "B" => Spec (CommRingCat.of k)
local notation "J" => SmoothSite.zariskiTopology B

set_option backward.isDefEq.respectTransparency false in
/-- Every positive Nisnevich cohomology class of a homotopy-invariant sheaf
with transfers has a Zariski covering sieve of zero restrictions. -/
theorem zeroSieve_mem_zariskiTopology_succ_of_perfect (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (n : ℕ) (X : SmoothSite B)
    (s : (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) (n + 1)).obj (op X)) :
    Presheaf.equalizerSieve
      (F := cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) (n + 1)) s 0 ∈ J X := by
  let Q := SheafCohomology.withTransfers k F (n + 1)
  have hQ : Q.IsA1Invariant :=
    (SheafCohomology.withTransfers_isA1Invariant_iff k F (n + 1)).mpr
      (isStrictA1Invariant_of_perfect F hF (n + 1))
  have hG : Q.HasGenericOpenZeros := by
    intro T _ _ a
    obtain ⟨W, hW, ha⟩ := exists_generic_open_restriction_eq_zero ((toSheaf k).obj F) n T a
    refine ⟨W, hW, ?_⟩
    change Q.transfer ((Cor.graphFunctor k).map (SmoothSite.openInclusion T W)) a = 0
    exact (SheafCohomology.withTransfers_graph k F (n + 1)
      (SmoothSite.openInclusion T W) a).trans ha
  have hcover := PresheafWithTransfers.zeroSieve_mem_zariskiTopology_of_generic_open_zeros
    Q hQ hG X s
  refine (J).superset_covering ?_ hcover
  intro Y f hf
  change Q.transfer ((Cor.graphFunctor k).map f) s =
    Q.transfer ((Cor.graphFunctor k).map f) 0 at hf
  change (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) (n + 1)).map f.op s =
    (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) (n + 1)).map f.op 0
  rw [map_zero] at hf ⊢
  exact (SheafCohomology.withTransfers_graph k F (n + 1) f s).symm.trans hf

end AlgebraicGeometry.SheafWithTransfers

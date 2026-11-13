/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.Ordinary
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.PerfectField
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.TransferInvariance

/-! # Strict A¹-invariance of the original transfer Ext presheaf -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian Opposite
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "π" => projection (SmoothSite.additiveGroupObject S)

variable [PerfectField k]
  [ordinaryExt : HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]

set_option maxSynthPendingDepth 4 in
/-- The original signed transfer Ext restriction along the affine projection is invertible. -/
theorem isIso_transferExt_projection (X : SmoothSite S) (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (n : ℕ) :
    let transferExt : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) :=
      hasExt_of_enoughInjectives _
    IsIso ((@transferExtPresheaf.{u + 1, u} k _ transferExt F n).map
      ((Cor.graphFunctor k).map ((π).app X)).op) := by
  intro transferExt
  let : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) := transferExt
  let f := ((π).app X).op
  let H := (Cor.graphFunctor k).op ⋙ (@transferExtPresheaf.{u + 1, u} k _ transferExt F n)
  let W := @SheafCohomology.withTransfers.{u + 1, u} k _ ordinaryExt F n
  let g := (PresheafWithTransfers.toPresheaf k).obj W
  have hW : W.IsA1Invariant :=
    (@SheafCohomology.withTransfers_isA1Invariant_iff.{u + 1, u} k _ ordinaryExt F n).2
      ((@isStrictA1Invariant_of_perfect k _ _ ordinaryExt F hF) n)
  have hg : IsIso (g.map f) := hW X
  let d : H ≅ g := NatIso.ofComponents
    (fun V => (@transferExtEquiv.{u + 1, u + 1, u}
      k _ transferExt ordinaryExt V.unop F n).toAddCommGrpIso) (by
    intro X Y b
    ext x
    exact (@ordinaryCohomologyTransfers_apply.{u + 1, u + 1, u}
      k _ transferExt ordinaryExt F n _ _ ((Cor.graphFunctor k).map b.unop) x).symm)
  exact (NatIso.isIso_map_iff d f).2 hg

end AlgebraicGeometry.SheafWithTransfers

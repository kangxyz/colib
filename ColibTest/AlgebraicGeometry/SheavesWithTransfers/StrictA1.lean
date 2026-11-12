/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.StrictInvariance
import Mathlib.Algebra.Field.Rat

/-! # Consumers of the ordinary strict affine-line invariance theorem -/

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.SmoothSite.Contraction Stacks.Cohomology.FreeYonedaUnivLE

universe u

noncomputable section

section ArbitraryField

variable {k : Type u} [Field k]

example (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ((PresheafWithTransfers.nisnevichSheafify k).obj P).obj.IsA1Invariant :=
  P.nisnevichSheafify_isA1Invariant hP

end ArbitraryField

section FiniteField

variable {k : Type u} [Field k] [Finite k]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    IsIso ((cohomologyPresheaf.{u + 1, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 0).map
      ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op) :=
  (SheafWithTransfers.isStrictA1Invariant_iff F).mp (F.isStrictA1Invariant_of_perfect hF) 0 X

end FiniteField

section RationalField

local notation "S" => (Spec (CommRingCat.of ℚ))
local notation "π" => (projection (SmoothSite.additiveGroupObject S))

variable [HasExt.{1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{1})]

example (P : PresheafWithTransfers.{1} ℚ) (hP : P.IsA1Invariant)
    (n : ℕ) (X : SmoothSite S) :
    IsIso ((cohomologyPresheaf.{1, 1}
      ((SheafWithTransfers.toSheaf ℚ).obj ((PresheafWithTransfers.nisnevichSheafify ℚ).obj P))
      (n + 1)).map ((π).app X).op) :=
  (P.nisnevichSheafify_isStrictA1Invariant hP) (n + 1) X

example (F : SheafWithTransfers.{1} ℚ) (n : ℕ) {X Y : SmoothSite S} (f : X ⟶ Y) :
    let H := cohomologyPresheaf.{1, 1} ((SheafWithTransfers.toSheaf ℚ).obj F) n
    H.map f.op ≫ H.map ((π).app X).op =
      H.map ((π).app Y).op ≫ H.map (affineLineCylinder.map f).op := by
  let H := cohomologyPresheaf.{1, 1} ((SheafWithTransfers.toSheaf ℚ).obj F) n
  change H.map f.op ≫ H.map ((π).app X).op =
    H.map ((π).app Y).op ≫ H.map (affineLineCylinder.map f).op
  have hp : affineLineCylinder.map f ≫ (π).app Y = (π).app X ≫ f :=
    (π).naturality f
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  exact congrArg (fun g : affineLineCylinder.obj X ⟶ Y ↦ H.map g.op) hp.symm

end RationalField

end

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.ChangeOfTopology
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.LocalZero

/-!
# Zariski to Nisnevich cohomology of sheaves with transfers

This is the canonical comparison for a Nisnevich sheaf with transfers and the
same coefficient sheaf read in the Zariski topology. Over a perfect field,
the comparison for homotopy-invariant coefficients is the transfer-sheaf
case of Voevodsky, *Cohomological theory of presheaves with transfers*,
§ 5.2, Theorem 5.7. See also Mazza–Voevodsky–Weibel, Proposition 13.9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Ordinary abelian sheaves on the smooth Zariski site have enough injectives. -/
instance zariskiSheaf_isGrothendieckAbelian (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (zariskiTopology S) AddCommGrpCat.{u + 1}) := by
  let : EssentiallySmall.{u + 1} (SmoothSite S) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall (zariskiTopology S) AddCommGrpCat.{u + 1}

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

local notation "B" => Spec (CommRingCat.of k)
local notation "J" => SmoothSite.zariskiTopology B
local notation "K" => SmoothSite.nisnevichTopology B
set_option hygiene false in
set_option quotPrecheck false in
local notation "A" => AddCommGrpCat.{u + 1}
local notation "P" => SmoothSite.nisnevichToZariskiSheaf B A

/-- The canonical map from Zariski to Nisnevich cohomology in the existing
ordinary cohomology presheaves on smooth schemes. -/
def zariskiCohomologyComparison (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    cohomologyPresheaf.{u + 1, u + 1} ((P).obj ((toSheaf k).obj F)) n ⟶
      cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) n :=
  (cohomologyPresheafChangeOfTopology.{u + 1} J K n).app ((toSheaf k).obj F)

/-- The change-of-topology map commutes with maps of the coefficient sheaves. -/
theorem zariskiCohomologyComparison_naturality_coeff
    {F G : SheafWithTransfers.{u + 1} k} (f : F ⟶ G) (n : ℕ) :
    (cohomologyPresheafFunctor.{u + 1, u + 1} J n).map ((P).map ((toSheaf k).map f)) ≫
        zariskiCohomologyComparison k G n =
      zariskiCohomologyComparison k F n ≫
        (cohomologyPresheafFunctor.{u + 1, u + 1} K n).map ((toSheaf k).map f) :=
  (cohomologyPresheafChangeOfTopology.{u + 1} J K n).naturality ((toSheaf k).map f)

/-- The comparison commutes with restriction along smooth-site morphisms,
including the inclusion of any open subscheme. -/
theorem zariskiCohomologyComparison_naturality
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ) {X Y : SmoothSite B} (f : X ⟶ Y) :
    (cohomologyPresheaf.{u + 1, u + 1} ((P).obj ((toSheaf k).obj F)) n).map f.op ≫
        (zariskiCohomologyComparison k F n).app (op X) =
      (zariskiCohomologyComparison k F n).app (op Y) ≫
        (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) n).map f.op :=
  (zariskiCohomologyComparison k F n).naturality f.op

variable [PerfectField k]

/-- Over a perfect field the canonical Zariski-to-Nisnevich map is an
isomorphism of ordinary cohomology presheaves in every degree. -/
@[colib_tag "COL-1307", colib_ref "Voevodsky2000CohomologicalTransfers" "Theorem 5.7"
  "specialization" "Homotopy-invariant Nisnevich sheaves with transfers over a perfect field",
  colib_ref "MVW2006" "Proposition 13.9" "comparison"
  "Canonical ordinary cohomology comparison for a homotopy-invariant Nisnevich transfer sheaf"]
theorem isIso_zariskiCohomologyComparison (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (n : ℕ) : IsIso (zariskiCohomologyComparison k F n) := by
  refine isIso_cohomologyPresheafChangeOfTopology_app.{u + 1} J K ((toSheaf k).obj F) n ?_
  intro p hp _
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  refine isZero_rightDerived_changeOfTopology_of_isZero_sheafify_cohomology.{u + 1}
    J K ((toSheaf k).obj F) (m + 1) ?_
  let := SmoothSite.wEqualsLocallyBijective_addCommGrpCat J
  exact Presheaf.isZero_sheafify_of_locally_zero J
    (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) (m + 1))
    (zeroSieve_mem_zariskiTopology_succ_of_perfect k F hF m)

/-- Evaluation of the canonical comparison at any smooth scheme is an
isomorphism on its ordinary cohomology groups. -/
theorem isIso_zariskiCohomologyComparison_app (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (n : ℕ) (X : SmoothSite B) :
    IsIso ((zariskiCohomologyComparison k F n).app (op X)) := by
  have := isIso_zariskiCohomologyComparison k F hF n
  infer_instance

end AlgebraicGeometry.SheafWithTransfers

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.Pages
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.Boundary
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata

/-! # Point support groups and the first coniveau differential -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [UnivLE.{u, w'}]
  (X : SmoothSite (Spec (.of k))) (K : EffectiveMotivesMinus k)

local notation "E" => coniveauSpectralSequence k X K

/-- The first page is the direct sum of the original cohomology groups
supported at the points of codimension `p`. Here `n` is the total degree. -/
@[no_expose, colib_tag "COL-1318"]
def coniveauFirstPagePointSumIso (p : ℕ) (n : ℤ) :
    ((E).page 1).X ((p : ℤ), n - p) ≅
      ∐ fun x : ConiveauPoints k X p ↦ pointSupportCohomology k X K n x.1 :=
  coniveauFirstPageWindowIso k X K p n ≪≫ (coniveauWindowPointSumIso k X K n p).symm

/-- The first differential is the original signed localization boundary
followed by projection to the next relative support layer. -/
@[colib_tag "COL-1318"]
theorem coniveauFirstPage_d_comp_windowIso_hom_eq (p : ℕ) (n : ℤ) :
    ((E).page 1).d ((p : ℤ), n - p) ((↑(p + 1) : ℤ), n + 1 - (↑(p + 1) : ℤ)) ≫
        (coniveauFirstPageWindowIso k X K (p + 1) (n + 1)).hom =
      (coniveauFirstPageWindowIso k X K p n).hom ≫
        coniveauWindowBoundary k X K n (Nat.le_succ p) ≫
          coniveauCohomologyToWindow k X K (n + 1) (p + 1) (p + 1 + 1) := by
  rw [coniveauFirstPage_d_comp_windowIso_hom, coniveauWindowConnecting_eq_boundary]

end AlgebraicGeometry.MotivicHomotopy

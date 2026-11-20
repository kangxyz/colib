/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.SpectralSequence.DecreasingFiltration
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.ConiveauObject

/-! # Pages of the motivic coniveau spectral sequence -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian.SpectralObject CategoryTheory.ComposableArrows
open CategoryTheory.Limits AlgebraicGeometry.Scheme Opposite OrderDual

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

/-- The decreasing codimension filtration, extended by stage zero to negative bounds. -/
def coniveauIndex : ℤ →o ℕᵒᵈ where
  toFun i := toDual (-i).toNat
  monotone' := fun _ _ h ↦ Int.toNat_le_toNat (neg_le_neg h)

theorem coniveauFirstPageIndex₁ (p : ℕ) (q : ℤ) :
    toDual (p + 1) = (coreE₁DecreasingFiltration coniveauIndex).i₁ ((p : ℤ), q) := by
  apply toDual_inj.mpr
  change p + 1 = (-(-(p : ℤ) - 1)).toNat
  omega

theorem coniveauFirstPageIndex₂ (p : ℕ) (q : ℤ) :
    toDual p = (coreE₁DecreasingFiltration coniveauIndex).i₂ ((p : ℤ), q) := by
  apply toDual_inj.mpr
  change p = (-(-(p : ℤ))).toNat
  omega

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [UnivLE.{u, w'}]
  (X : SmoothSite (Spec (.of k))) (K : EffectiveMotivesMinus k)

/-- The coniveau spectral sequence starts with the adjacent support windows of the
original effective pair cohomology. The page differential has bidegree `(r, 1-r)`. -/
@[colib_tag "COL-1318", colib_ref "Deglise2011Coniveau" "Definition 1.6"
  "adaptation" "The spectral object of codimension windows for represented effective cohomology"]
def coniveauSpectralSequence : CohomologicalSpectralSequence AddCommGrpCat.{w'} 1 :=
  (coniveauSpectralObject k X K).spectralSequence (coreE₁DecreasingFiltration coniveauIndex)

local notation "data" => coreE₁DecreasingFiltration coniveauIndex
local notation "S" => coniveauSpectralObject k X K
local notation "E" => coniveauSpectralSequence k X K

private def coniveauFirstPageObjectIso (p : ℕ) (n : ℤ) :
    ((E).page 1).X ((p : ℤ), n - p) ≅
      ((S).H n).obj (mk₁ (homOfLE (toDual_le_toDual.mpr (Nat.le_succ p)))) :=
  (S).spectralSequenceFirstPageXIso (data) ((p : ℤ), n - p) _ _
    (coniveauFirstPageIndex₁ p _) (coniveauFirstPageIndex₂ p _) n (by
      simp only [coreE₁DecreasingFiltration_deg]
      omega)

/-- At codimension `p` the first page is the original relative window between
codimension bounds `p` and `p+1`, in total cohomological degree `n`. -/
@[no_expose]
def coniveauFirstPageWindowIso (p : ℕ) (n : ℤ) :
    ((E).page 1).X ((p : ℤ), n - p) ≅ coniveauRelativeSupportCohomology k X K n p (p + 1) :=
  coniveauFirstPageObjectIso k X K p n ≪≫
    coniveauSpectralObjectWindowIso k X K n p (p + 1) (Nat.le_succ p)

private theorem coniveauFirstPage_d_comp_objectIso (p : ℕ) (n : ℤ) :
    ((E).page 1).d ((p : ℤ), n - p) ((↑(p + 1) : ℤ), n + 1 - (↑(p + 1) : ℤ)) ≫
        (coniveauFirstPageObjectIso k X K (p + 1) (n + 1)).hom =
      (coniveauFirstPageObjectIso k X K p n).hom ≫ (S).δ
        (homOfLE (toDual_le_toDual.mpr (Nat.le_succ (p + 1))))
        (homOfLE (toDual_le_toDual.mpr (Nat.le_succ p))) n (n + 1) := by
  have hrel : (ComplexShape.up' ((1, 1 - 1) : ℤ × ℤ)).Rel
      ((p : ℤ), n - p) ((↑(p + 1) : ℤ), n + 1 - (↑(p + 1) : ℤ)) := by
    change _ + ((1, 1 - 1) : ℤ × ℤ) = _
    ext <;> simp
  have hd := (S).spectralSequence_first_page_d_eq (data) _ _ hrel
    (toDual (p + 1 + 1)) (toDual (p + 1)) (toDual p)
    (coniveauFirstPageIndex₁ (p + 1) _) (coniveauFirstPageIndex₁ p _)
    (coniveauFirstPageIndex₂ p _) n (n + 1) (by
      simp only [coreE₁DecreasingFiltration_deg]
      omega) rfl
  change _ = (coniveauFirstPageObjectIso k X K p n).hom ≫ _ ≫
    (coniveauFirstPageObjectIso k X K (p + 1) (n + 1)).inv at hd
  let e := coniveauFirstPageObjectIso k X K (p + 1) (n + 1)
  exact e.eq_comp_inv.mp (hd.trans (Category.assoc _ _ _).symm)

/-- The first-page comparison carries the differential to the window connecting map. -/
theorem coniveauFirstPage_d_comp_windowIso_hom (p : ℕ) (n : ℤ) :
    ((E).page 1).d ((p : ℤ), n - p) ((↑(p + 1) : ℤ), n + 1 - (↑(p + 1) : ℤ)) ≫
        (coniveauFirstPageWindowIso k X K (p + 1) (n + 1)).hom =
      (coniveauFirstPageWindowIso k X K p n).hom ≫
        coniveauWindowConnecting k X K n (n + 1) rfl (Nat.le_succ p) (Nat.le_succ (p + 1)) := by
  simp only [coniveauFirstPageWindowIso, Iso.trans_hom, ← Category.assoc,
    coniveauFirstPage_d_comp_objectIso]
  have h := coniveauSpectralObject_δ_windowIso k X K n (n + 1) rfl
    (Nat.le_succ p) (Nat.le_succ (p + 1))
  simpa only [Category.assoc] using
    congrArg ((coniveauFirstPageObjectIso k X K p n).hom ≫ ·) h

/-- The first page has zero terms in negative codimension. -/
theorem isZero_coniveauFirstPageX_of_lt_zero (p q : ℤ) (hp : p < 0) :
    IsZero (((coniveauSpectralSequence k X K).page 1).X (p, q)) := by
  let z := toDual (0 : ℕ)
  have h₁ : z = (data).i₁ (p, q) := by
    apply toDual_inj.mpr
    change 0 = (-(-p - 1)).toNat
    omega
  have h₂ : z = (data).i₂ (p, q) := by
    apply toDual_inj.mpr
    change 0 = (-(-p)).toNat
    omega
  let e := (S).spectralSequenceFirstPageXIso (data) (p, q) z z h₁ h₂ (p + q) rfl
  exact ((S).isZero_H_map_mk₁_of_isIso (p + q) (𝟙 z)).of_iso e

end AlgebraicGeometry.MotivicHomotopy

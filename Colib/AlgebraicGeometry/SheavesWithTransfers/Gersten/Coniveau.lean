/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.SpectralSequence.SingleRow
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.Convergence
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.Basic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.Opens

/-! # The coniveau spectral sequence of a homotopy-invariant sheaf with transfers -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme Opposite TopologicalSpace
open Stacks.Cohomology.FreeYonedaUnivLE

universe u w

namespace AlgebraicGeometry.SheafWithTransfers.Gersten

open MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] effectiveSupportCoefficientCorSheafify
  effectiveSupportCoefficientSmoothSheafify hasSheafify_zariskiOpens hasExt_zariskiOpens

/-- Use the canonical abelian structure on the original Nisnevich transfer coefficients. -/
local instance coniveauTransferAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{u + 1} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{u + 1} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

local notation "K" => effectiveHICoefficient k F hF
local notation "E" => coniveauSpectralSequence k X (K)

/-- Point purity concentrates the first page of the coniveau spectral
sequence of a homotopy-invariant transfer sheaf in row zero. -/
@[colib_tag "COL-1319", colib_ref "Voevodsky2000CohomologicalTransfers" "Lemma 4.36"
  "ingredient" "Point concentration in the codimension degree"]
theorem isZero_coniveauFirstPageX_of_ne_zero_row (pq : ℤ × ℤ) (hq : pq.2 ≠ 0) :
    IsZero (((E).page 1).X pq) := by
  obtain ⟨p, q⟩ := pq
  by_cases hp : p < 0
  · exact isZero_coniveauFirstPageX_of_lt_zero k X (K) p q hp
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hp)
  have h := isZero_coniveauWindow_of_degree_ne_codimension k F hF X p ((p : ℤ) + q)
    (by change q ≠ 0 at hq; omega)
  simpa only [add_sub_cancel_left] using
    h.of_iso (coniveauFirstPageWindowIso k X (K) p ((p : ℤ) + q))

/-- Every coniveau page of the original degree-zero coefficient is concentrated in row zero. -/
theorem isZero_coniveauPageX_of_ne_zero_row (r : ℤ) (hr : 1 ≤ r) (a : ℤ × ℤ) (ha : a.2 ≠ 0) :
    IsZero (((E).page r hr).X a) :=
  (E).isZero_page_X_of_ne_zero_row (isZero_coniveauFirstPageX_of_ne_zero_row k X F hF) r hr a ha

/-- All differentials from the second page on vanish. -/
@[colib_tag "COL-1319"]
theorem coniveauPage_d_eq_zero_of_two_le (r : ℤ) (hr : 2 ≤ r) (a b : ℤ × ℤ) :
    ((E).page r (by omega)).d a b = 0 :=
  (E).page_d_eq_zero_of_single_row (isZero_coniveauFirstPageX_of_ne_zero_row k X F hF) r hr a b

/-- The native page homology isomorphisms identify every page from the
second on with the second page at each bidegree. -/
@[no_expose, colib_tag "COL-1319"]
def coniveauPageXIsoSecond (r : ℤ) (hr : 2 ≤ r) (a : ℤ × ℤ) :
    ((E).page r (by omega)).X a ≅ ((E).page 2).X a :=
  (E).pageXIsoOfSingleRow (isZero_coniveauFirstPageX_of_ne_zero_row k X F hF) r hr a

private theorem epi_coniveauTransition_succ (i n : ℕ) (hi : i ≠ n) :
    Epi (coniveauCohomologyTransition k X (K) (n : ℤ) (Nat.le_succ i)) :=
  (coniveauCohomologyStage_exact k X (K) (n : ℤ) (Nat.le_succ i)).epi_f
    ((isZero_coniveauWindow_of_ne k F hF X i n hi).eq_of_tgt _ _)

private theorem isZero_coniveauStage_of_degree_lt (n a d : ℕ)
    (hd : topologicalKrullDim X.left ≤ d) (hna : n < a) :
    IsZero (coniveauCohomology k X (K) (n : ℤ) a) := by
  have descend (length : ℕ) : ∀ i, n < i → d < i + length →
      IsZero (coniveauCohomology k X (K) (n : ℤ) i) := by
    induction length with
    | zero =>
      intro i _ hi
      exact isZero_coniveauCohomology_above_dimension k X (K) (n : ℤ) hd
        (by simpa only [Nat.add_zero] using hi)
    | succ length ih =>
      intro i hni hi
      let f := coniveauCohomologyTransition k X (K) (n : ℤ) (Nat.le_succ i)
      let : Epi f := epi_coniveauTransition_succ k X F hF i n (by omega)
      exact IsZero.of_epi f (ih (i + 1) (by omega) (by omega))
  exact descend (d + 1) a hna (by omega)

private theorem epi_coniveauTransition_zero_of_le_degree (n a : ℕ) (ha : a ≤ n) :
    Epi (coniveauCohomologyTransition k X (K) (n : ℤ) (Nat.zero_le a)) := by
  induction a with
  | zero =>
    have h : coniveauCohomologyTransition k X (K) (n : ℤ) (Nat.zero_le 0) = 𝟙 _ := by
      apply colimit.hom_ext
      intro Z
      rw [ι_coniveauCohomologyTransition, Category.comp_id]
      rfl
    rw [h]
    infer_instance
  | succ a ih =>
    let : Epi (coniveauCohomologyTransition k X (K) (n : ℤ) (Nat.zero_le a)) :=
      ih (by omega)
    let : Epi (coniveauCohomologyTransition k X (K) (n : ℤ) (Nat.le_succ a)) :=
      epi_coniveauTransition_succ k X F hF a n (by omega)
    rw [← coniveauCohomologyTransition_comp k X (K) (n : ℤ) (Nat.zero_le a) (Nat.le_succ a)]
    infer_instance

/-- At cohomological degree `n` the coniveau filtration is full through stage `n`. -/
@[colib_tag "COL-1319"]
theorem coniveauFiltration_eq_top_of_le_degree (n a : ℕ) (ha : a ≤ n) :
    coniveauFiltration k X (K) (n : ℤ) a = ⊤ :=
  coniveauFiltration_eq_top_of_epi k X (K) (n : ℤ) a
    (epi_coniveauTransition_zero_of_le_degree k X F hF n a ha)

/-- At cohomological degree `n` the coniveau filtration is zero above stage `n`. -/
@[colib_tag "COL-1319"]
theorem coniveauFiltration_eq_bot_of_degree_lt (n a : ℕ) (ha : n < a) :
    coniveauFiltration k X (K) (n : ℤ) a = ⊥ := by
  obtain ⟨d, hd⟩ := SmoothSite.exists_nat_topologicalKrullDim_le k X
  exact coniveauFiltration_eq_bot_of_isZero k X (K) (n : ℤ) a
    (isZero_coniveauStage_of_degree_lt k X F hF n a d hd ha)

private def effectiveSmoothZariskiCohomologyIso (n : ℕ) :
    AddCommGrpCat.of ((effectiveSmoothMotive k).obj X ⟶ (K)⟦(n : ℤ)⟧) ≅
      (cohomologyPresheaf.{u + 1, u + 1} (zariskiSheafOnOpens k X F) n).obj
        (op (⊤ : X.left.Opens)) := by
  let G := SmoothSite.opensFunctor X
  let P := cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) n
  let i : G.obj ⊤ ⟶ X := SmoothSite.openInclusion X ⊤
  let : IsIso ((SmoothSite.forgetScheme (Spec (.of k))).map i) :=
    inferInstanceAs (IsIso X.left.topIso.hom)
  let : IsIso i := isIso_of_reflects_iso i (SmoothSite.forgetScheme (Spec (.of k)))
  let e : coniveauAbutment k X (K) (n : ℤ) ≅ P.obj (op X) :=
    (effectiveSmoothCohomologyEquiv k X F hF n).toAddCommGrpIso
  let c := (zariskiCohomologyOnOpensIso k X F hF n).app (op (⊤ : X.left.Opens))
  exact e ≪≫ P.mapIso (asIso i).op ≪≫ c.symm

/-- The degree-`(p,0)` term on the second coniveau page is the ordinary
Zariski cohomology of the original transfer coefficient in degree `p`. -/
@[no_expose, colib_tag "COL-1319", colib_ref "Deglise2011Coniveau" "Equation (2.13.a)"
  "adaptation" "Ordinary Zariski cohomology for the degree-zero effective transfer coefficient"]
def coniveauSecondPageZariskiCohomologyIso (p : ℕ) :
    ((E).page 2).X ((p : ℤ), 0) ≅
      (cohomologyPresheaf.{u + 1, u + 1} (zariskiSheafOnOpens k X F) p).obj
        (op (⊤ : X.left.Opens)) := by
  classical
  let hX := SmoothSite.exists_nat_topologicalKrullDim_le k X
  let d := Nat.find hX
  have hd : topologicalKrullDim X.left ≤ d := Nat.find_spec hX
  let r : ℤ := (d : ℤ) + 2
  have hr : 2 ≤ r := by dsimp [r]; omega
  let e := coniveauPageXIsoSecond k X F hF r hr ((p : ℤ), 0)
  let s := coniveauSpectralSequencePageStableIso k X (K) r (by omega) p 0 hd
    (by dsimp [r]; omega)
  let gr := coniveauAssociatedGradedIsoOfIsZeroOfEpi k X (K) (p : ℤ) p
    (isZero_coniveauStage_of_degree_lt k X F hF p (p + 1) d hd (Nat.lt_succ_self p))
    (epi_coniveauTransition_zero_of_le_degree k X F hF p p le_rfl)
  exact e.symm ≪≫ s ≪≫ gr ≪≫ effectiveSmoothZariskiCohomologyIso k X F hF p

end AlgebraicGeometry.SheafWithTransfers.Gersten

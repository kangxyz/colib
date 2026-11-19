/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.CousinSheaves.Window
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.PointPurity
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.Resolution
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # The Gersten resolution for a homotopy-invariant sheaf with transfers -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme Opposite TopologicalSpace
universe u w

namespace AlgebraicGeometry.SheafWithTransfers.Gersten

open AlgebraicGeometry.Gersten MotivicHomotopy

attribute [local instance] hasSheafify_zariskiOpens

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] effectiveSupportCoefficientCorSheafify
  effectiveSupportCoefficientSmoothSheafify

/-- Use the canonical abelian structure on the Nisnevich transfer coefficients. -/
local instance gerstenBasicAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{u + 1} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{u + 1} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
set_option hygiene false in
set_option quotPrecheck false in
local notation "Ab" => AddCommGrpCat.{u + 1}

variable (X : SmoothSite (Spec (CommRingCat.of k)))
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

local notation "K" => effectiveHICoefficient k F hF
local notation "J" => _root_.Opens.grothendieckTopology X.left.carrier

/-- Point purity and the disjoint-support comparison force every off-diagonal
support window of a homotopy-invariant transfer sheaf to vanish. -/
theorem isZero_coniveauWindow_of_ne (Y : SmoothSite S) (p n : ℕ) (h : p ≠ n) :
    IsZero (coniveauRelativeSupportCohomology k Y K (n : ℤ) p (p + 1)) := by
  let A := fun x : ConiveauPoints k Y p ↦ pointSupportCohomology k Y K (n : ℤ) x.1
  have hA : IsZero (∐ A) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply Sigma.hom_ext
    intro x
    exact (isZero_pointSupportCohomology_of_ne k Y x.1 F hF x.2 (n : ℤ) (by
      exact_mod_cast h.symm)).eq_of_src _ _
  exact hA.of_iso (coniveauWindowPointSumIso k Y K (n : ℤ) p).symm

local notation "H" => fun U p n h ↦
  isZero_coniveauWindow_of_ne k F hF (Functor.obj (SmoothSite.opensFunctor X) U) p n h

/-- The Gersten complex has the original localization differentials on the
degree-codimension diagonal of the support tower. -/
abbrev gerstenComplex : CochainComplex (Sheaf J Ab) ℕ :=
  zariskiCousinComplex k X F hF H

/-- The augmentation is induced by restriction from the original coefficient
to the codimension-zero support window. -/
abbrev gerstenAugmentation : zariskiSheafOnOpens k X F ⟶ (gerstenComplex k X F hF).X 0 :=
  zariskiCousinAugmentation k X F hF H

/-- The original coefficient is the kernel of the first Gersten differential. -/
@[colib_tag "COL-1310", no_expose]
def gerstenAugmentationIsKernel :
    IsLimit (KernelFork.ofι (gerstenAugmentation k X F hF)
      (zariskiCousinAugmentation_comp_d k X F hF H)) :=
  zariskiCousinAugmentationIsKernel k X F hF H

/-- Sections on every Zariski open are the kernel of the first differential
on that open. -/
@[colib_tag "COL-1310", no_expose]
def gerstenSectionsAugmentationIsKernel (U : X.left.Opens) :
    let E := sheafToPresheaf J Ab ⋙ (CategoryTheory.evaluation _ _).obj (op U)
    IsLimit ((KernelFork.ofι (gerstenAugmentation k X F hF)
      (zariskiCousinAugmentation_comp_d k X F hF H)).map E) := by
  intro E
  exact KernelFork.mapIsLimit _ (gerstenAugmentationIsKernel k X F hF) E

/-- The Gersten complex is exact in each positive degree. -/
@[colib_tag "COL-1310", colib_ref "Voevodsky2000CohomologicalTransfers" "Theorem 4.37"
  "adaptation" "Exactness of the Cousin resolution for homotopy-invariant sheaves with transfers"]
theorem gerstenComplex_exactAt_succ (p : ℕ) :
    (gerstenComplex k X F hF).ExactAt (p + 1) :=
  zariskiCousinComplex_exactAt_succ k X F hF H p

/-- The Gersten complex terminates above a finite support bound for the scheme. -/
@[colib_tag "COL-1310"]
theorem gerstenComplex_isBounded :
    ∃ d : ℕ, ∀ p : ℕ, d < p → IsZero ((gerstenComplex k X F hF).X p) := by
  let T := zariskiSupportTower k X F hF H
  exact ⟨T.dimension, T.isZero_cochainComplex_X_of_dimension_lt⟩

/-- The degree-`p` term is the coproduct sheaf of codimension-`p` point
supports. Its coefficients are identified by point purity. -/
@[colib_tag "COL-1310", no_expose]
def gerstenTermIso (p : ℕ) :
    (gerstenComplex k X F hF).X p ≅ coniveauCousinPointSheaf k X K p (p : ℤ) :=
  let a := presheafToSheaf J Ab
  a.mapIso (coniveauWindowCousinPresheafIso k X K p (p : ℤ)).symm ≪≫
    asIso ((sheafificationAdjunction J Ab).counit.app _)

/-- The point coproduct description makes each term of Gersten flasque. -/
@[colib_tag "COL-1310"]
theorem gerstenTerm_isFlasque (p : ℕ) :
    TopCat.Sheaf.IsFlasque (X := X.left.carrier) ((gerstenComplex k X F hF).X p) := by
  let e := (sheafToPresheaf J Ab).mapIso (gerstenTermIso k X F hF p)
  constructor
  intro U V f
  have he := e.hom.naturality f
  have h := congrArg (· ≫ e.inv.app V) he
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at h
  change Epi (((sheafToPresheaf J Ab).obj ((gerstenComplex k X F hF).X p)).map f)
  rw [h]
  let W := coniveauCousinPointSheaf k X K p (p : ℤ)
  let : Epi (((sheafToPresheaf J Ab).obj W).map f) := by
    change Epi (W.obj.map f)
    exact TopCat.Presheaf.IsFlasque.epi f
  let : IsIso (e.hom.app U) := (e.app U).isIso_hom
  let : IsIso (e.inv.app V) := (e.app V).isIso_inv
  infer_instance

end AlgebraicGeometry.SheafWithTransfers.Gersten

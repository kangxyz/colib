/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.UnitOpen
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ChartBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionBoundaryMaps

/-!
# The marked inverse boundary of the correction parameter

The whole marked and residual pieces cover the original finite inverse
fiber. Their source maps factor through the two original correction
boundary maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X P A C Y Z D : Scheme.{u}}
  (q : X ⟶ S) (π : P ⟶ S) (jA : X ⟶ P) (hA : jA ≫ π = q) (a : A ⟶ X)
  (f : C ⟶ P) [IsFinite f] (j : Y ⟶ C)
  (p : Y ⟶ X) (hB : j ≫ (f ≫ π) = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (H : IsPullback s (𝟙 Z) (j ≫ f) (z ≫ jA)) (d : D ⟶ C)

local notation "b" => (a ≫ q)
local notation "zA" => (z ≫ jA)
local notation "F" => (retainedProductInclusion b π f)
local notation "mZ" => (retainedProductInclusion b π zA)
local notation "hmark" => (markedSection_original_equation f j zA s H)
local notation "B" => (pullback (pullback.snd b (f ≫ π)) d ⨿ pullback b (z ≫ q))
local notation "iN" => (psiBoundaryInclusion q (f ≫ π) j p hB a z s hs d)

include hA in
/-- The actual two inverse marked pieces cover the fiber and factor through
the entire original correction boundary. -/
theorem exists_correctionMarkedBoundary_cover
    (bE : (residualMarkedFiberOpen f j zA s hmark).toScheme ⟶ D)
    (hbE : bE ≫ d = residualMarkedFiberMap f j zA s hmark) :
    ∃ (W : Bool → Scheme.{u}) (l : ∀ i, W i ⟶ pullback F mZ) (v : ∀ i, W i ⟶ B),
      (∀ x : (pullback F mZ : Scheme.{u}), ∃ i, x ∈ Set.range (l i)) ∧
      ∀ i, l i ≫ pullback.fst F mZ = v i ≫ iN := by
  let J := retainedProductInclusion b (f ≫ π) j
  let s₀ := productMarkedSection b π f zA j s H
  let H₀ := productMarkedSection_isPullback b π f zA j s H
  let h₀ := markedSection_original_equation F J mZ s₀ H₀
  let t : pullback b (zA ≫ π) ⟶ pullback F mZ := markedFiberSection F J mZ s₀ h₀
  let R : (pullback F mZ : Scheme.{u}).Opens := residualMarkedFiberOpen F J mZ s₀ h₀
  let m := correctionMarkBaseIso q π jA hA a z
  let vZ : pullback b (zA ≫ π) ⟶ B := m.hom ≫ coprod.inr
  have hZ : t ≫ pullback.fst F mZ = vZ ≫ iN := by
    rw [show t ≫ pullback.fst F mZ = s₀ ≫ J from markedFiberSection_fst F J mZ s₀ h₀]
    simpa only [vZ, Category.assoc, psiBoundaryInclusion, coprod.inr_desc] using
      (correctionMarkToSourceProduct_map q π jA hA a f j p hB z s hs H).symm
  obtain ⟨vE, hvE⟩ := exists_productResidualBoundary_factor b π f j zA s H d bE hbE
  let vR : R.toScheme ⟶ B := vE ≫ coprod.inl
  have hR : R.ι ≫ pullback.fst F mZ = vR ≫ iN := by
    calc
      _ = vE ≫ pullback.fst (pullback.snd b (f ≫ π)) d := hvE
      _ = _ := by simp only [vR, Category.assoc, psiBoundaryInclusion, coprod.inl_desc]
  let W : Bool → Scheme.{u} := Bool.rec R.toScheme (pullback b (zA ≫ π))
  let l : ∀ i, W i ⟶ pullback F mZ := Bool.rec R.ι t
  let v : ∀ i, W i ⟶ B := Bool.rec vR vZ
  refine ⟨W, l, v, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Set.range t
    · exact ⟨true, hx⟩
    · refine ⟨false, ?_⟩
      change x ∈ Set.range R.ι
      rw [Opens.range_ι]
      change x ∉ Set.range t
      exact hx
  · intro i
    cases i
    · exact hR
    · exact hZ

include hA in
/-- The unit ideal on the original correction boundary pulls back to the
unit ideal on the entire inverse marked fiber. -/
theorem comap_eq_top_on_correctionMarkedBoundary
    (bE : (residualMarkedFiberOpen f j zA s hmark).toScheme ⟶ D)
    (hbE : bE ≫ d = residualMarkedFiberMap f j zA s hmark)
    (I : (pullback b (f ≫ π) : Scheme.{u}).IdealSheafData) (hI : I.comap iN = ⊤) :
    I.comap (pullback.fst F mZ) = ⊤ := by
  obtain ⟨W, l, v, hcover, hfactor⟩ :=
    exists_correctionMarkedBoundary_cover q π jA hA a f j p hB z s hs H d bE hbE
  apply IdealSheafData.eq_top_of_range_cover _ l hcover
  intro i
  rw [← IdealSheafData.comap_comp, hfactor, IdealSheafData.comap_comp, hI,
    IdealSheafData.comap_top]

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end

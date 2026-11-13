/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.AssociatedUnitGluing
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionNormBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionTargetBoundary

/-!
# The correction norm on the full marked boundary

The determinant comparison on free affine charts gives equality of the
source norm and target ratio on the whole marked scheme.

Adapted from `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Correction/NormalizedUnit.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

local instance {X : Scheme.{u}} (L : X.Modules) [hL : IsInvertibleModule X L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL

variable {S X Y P C A Z D₁ D₂ : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π]
  (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (a : A ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (d₂ : D₂ ⟶ P) (hd₂ : Disjoint (Set.range jA) (Set.range d₂))
  (ha : Disjoint (Set.range a) (Set.range z))
  (U : (pullback (a ≫ q) π : Scheme.{u}).Opens)

local notation "b" => (a ≫ q)
local notation "zA" => (z ≫ jA)
local notation "hA₀" => (hA.trans (Category.id_comp q))
local notation "Hmark" => (pairedMark_isPullback f j jA p hRet z s H)
local notation "hmark" => (markedSection_original_equation f j zA s Hmark)
local notation "F" => (retainedProductInclusion b π f)
local notation "τ" => (correctionTargetParameterMap q π jA hA₀ a)
local notation "iN" => (psiBoundaryInclusion q (f ≫ π) j p hB a z s hs d₁)
local notation "iA" => (fullGraphBoundaryMap π jA z d₂)
local notation "θA" => (fullGraphCoordinate q π jA (𝟙 X) hA z z (Category.comp_id z)
  IsPullback.of_id_snd e d₂ hd₂)
local notation "θN" => (fullCorrectionCoordinate q (f ≫ π) z e d₁ a ha)
local notation "mZ" => (retainedProductInclusion b π zA)

set_option maxHeartbeats 700000 in
-- The proof uses the original marked pullbacks on the affine chart cover.
/-- The original source norm and target coefficient agree on the full mark. -/
theorem correctionNormCoefficient_on_mark [IsClosedImmersion (z ≫ jA)]
    (bE : (residualMarkedFiberOpen f j zA s hmark).toScheme ⟶ D₁)
    (hbE : bE ≫ d₁ = residualMarkedFiberMap f j zA s hmark)
    (hF : IsFiniteLocallyFree F) (hG : IsFiniteLocallyFree (pullback.snd F U.ι))
    (lZ : pullback b (zA ≫ π) ⟶ U.toScheme) (hlZ : lZ ≫ U.ι = mZ)
    (cN : Γ((pullback F U.ι : Scheme.{u}), ⊤)) (cA : Γ(U.toScheme, ⊤))
    (hscalarN : ∀ {B : Scheme.{u}} (i : B ⟶ pullback F U.ι)
      (v : B ⟶ pullback (pullback.snd b (f ≫ π)) d₁ ⨿ pullback b (z ≫ q)),
      i ≫ pullback.fst F U.ι = v ≫ iN → i.appTop cN * v.appTop θN = 1)
    (hscalarA : ∀ {B : Scheme.{u}} (i : B ⟶ U.toScheme)
      (v : B ⟶ pullback (pullback.snd (jA ≫ π) π) d₂ ⨿ pullback (jA ≫ π) (z ≫ jA ≫ π)),
      i ≫ (U.ι ≫ τ) = v ≫ iA → i.appTop cA * v.appTop θA = 1) :
    lZ.appTop ((@normTop _ _ (pullback.snd F U.ι) hG) cN) = lZ.appTop cA := by
  let : IsFiniteLocallyFree F := hF
  let g := pullback.snd F U.ι
  let : IsFiniteLocallyFree g := hG
  choose V hV hxV hfree using exists_freeAffineNormChart F U
  let w (i : U.toScheme) := (V i).ι ≫ U.ι
  let k (i : U.toScheme) := pullback.snd mZ (w i)
  let kZ (i : U.toScheme) := pullback.fst mZ (w i)
  let : ∀ i, IsOpenImmersion (kZ i) := fun i => inferInstanceAs
    (IsOpenImmersion (pullback.fst mZ (w i)))
  have heq (i : U.toScheme) :
      (k i).appTop ((V i).ι.appTop (normTop g cN)) =
        (k i).appTop ((V i).ι.appTop cA) := by
    let : IsAffine (V i).toScheme := hV i
    have hn' := correctionSourceNorm_mark_on_chart q π f j jA p hRet hB hA₀ a z s hs H
      e d₁ ha U (V i) hF hG bE hbE (hfree i) cN hscalarN
    obtain ⟨v, hv, hθ⟩ := exists_correctionTargetMark_factor q π jA hA a z e d₂ hd₂ U
      (k i ≫ (V i).ι) (kZ i) (by
        rw [Category.assoc]
        exact (pullback.condition (f := mZ) (g := w i)).symm)
    have ht := hscalarA (k i ≫ (V i).ι) v hv
    rw [hθ, Hom.comp_appTop, CommRingCat.comp_apply] at ht
    let σ := (kZ i ≫ (correctionMarkBaseIso q π jA hA₀ a z).hom).appTop
      (correctionCoordinate q z e a)
    let t := (k i).appTop ((V i).ι.appTop cA)
    have ht' : t * σ = 1 := ht
    have hσ : IsUnit σ := ⟨⟨σ, t, (mul_comm σ t).trans ht', ht'⟩, rfl⟩
    exact hσ.mul_right_cancel (hn'.trans ht'.symm)
  have hcover (x : (pullback b (zA ≫ π) : Scheme.{u})) :
      ∃ i, x ∈ Set.range (kZ i) := by
    let y := lZ x
    have hx : mZ x = w y ⟨y, hxV y⟩ := congrArg (fun t => t x) hlZ.symm
    obtain ⟨a, ha, _⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback mZ (w y)) x ⟨y, hxV y⟩ hx
    exact ⟨y, a, ha⟩
  apply globalSections_eq_of_openImmersion_cover kZ hcover
  intro i
  have hcomp : kZ i ≫ lZ = k i ≫ (V i).ι := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, hlZ, Category.assoc]
    exact pullback.condition (f := mZ) (g := w i)
  have hrestrict (r : Γ(U.toScheme, ⊤)) :
      (kZ i).appTop (lZ.appTop r) = (k i).appTop ((V i).ι.appTop r) := by
    rw [← CommRingCat.comp_apply, ← Hom.comp_appTop, hcomp,
      Hom.comp_appTop, CommRingCat.comp_apply]
  rw [hrestrict, hrestrict]
  exact heq i

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end

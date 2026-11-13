/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Marked.Norm
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.BoundaryUnit
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ChartBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.FullBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedMarkedSquare

/-!
# The source norm on the marked correction chart

The original marked and residual maps factor through the two prescribed
correction boundaries. The finite free norm is computed on the actual
marked factor when the residual coefficient is one.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Stacks.Ample Stacks.Divisors Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X Y P C A Z D₁ : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] (jA : X ⟶ P) [IsOpenImmersion jA]
  (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = q)
  (a : A ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (ha : Disjoint (Set.range a) (Set.range z))
  (U : (pullback (a ≫ q) π : Scheme.{u}).Opens) (V : U.toScheme.Opens)

local notation "b" => (a ≫ q)
local notation "zA" => (z ≫ jA)
local notation "Hmark" => (pairedMark_isPullback f j jA p hRet z s H)
local notation "hmark" => (markedSection_original_equation f j zA s Hmark)
local notation "F" => (retainedProductInclusion b π f)
local notation "mZ" => (retainedProductInclusion b π zA)
local notation "iN" => (psiBoundaryInclusion q (f ≫ π) j p hB a z s hs d₁)
local notation "θN" => (fullCorrectionCoordinate q (f ≫ π) z e d₁ a ha)
local notation "u₁" => (pullback.fst F (Scheme.Opens.ι U))
local notation "gU" => (pullback.snd F (Scheme.Opens.ι U))
local notation "w" => (Scheme.Opens.ι V ≫ Scheme.Opens.ι U)
local notation "z₀" => (pullback.snd mZ w)
local notation "αZ" => (pullback.fst mZ w)
set_option quotPrecheck false in
local notation "σ" => ((αZ ≫ (correctionMarkBaseIso q π jA hA a z).hom).appTop
  (correctionCoordinate q z e a))

/-- The whole marked factor determines the norm of a section with the
prescribed correction boundary value. -/
theorem correctionSourceNorm_mark_on_chart
    [IsClosedImmersion (z ≫ jA)] [IsAffine V.toScheme]
    (hF : IsFiniteLocallyFree F) (hG : IsFiniteLocallyFree gU)
    (bE : (residualMarkedFiberOpen f j zA s hmark).toScheme ⟶ D₁)
    (hbE : bE ≫ d₁ = residualMarkedFiberMap f j zA s hmark)
    (hfree : letI : Algebra Γ(V.toScheme, ⊤) Γ((pullback F w : Scheme.{u}), ⊤) :=
      (pullback.snd F w).appTop.hom.toAlgebra
      Module.Free Γ(V.toScheme, ⊤) Γ((pullback F w : Scheme.{u}), ⊤))
    (r : Γ((pullback F U.ι : Scheme.{u}), ⊤))
    (hscalar : ∀ {B : Scheme.{u}} (i : B ⟶ pullback F U.ι)
      (v : B ⟶ pullback (pullback.snd b (f ≫ π)) d₁ ⨿ pullback b (z ≫ q)),
      i ≫ u₁ = v ≫ iN → i.appTop r * v.appTop θN = 1) :
    (z₀).appTop (V.ι.appTop ((@normTop _ _ gU hG) r)) * σ = 1 := by
  let : IsFiniteLocallyFree gU := hG
  let k := normQuotientBoundaryMap F U w V.ι rfl
  let gV := pullback.snd F w
  let : IsFiniteLocallyFree gV := isFiniteLocallyFree_pullback_snd F w hF
  let : Algebra Γ(V.toScheme, ⊤) Γ((pullback F w : Scheme.{u}), ⊤) := gV.appTop.hom.toAlgebra
  let : Module.Free Γ(V.toScheme, ⊤) Γ((pullback F w : Scheme.{u}), ⊤) := hfree
  let : IsClosedImmersion mZ :=
    MorphismProperty.of_isPullback (retainedProductInclusion_isPullback b π zA) inferInstance
  let : IsAffine (pullback mZ w) := isAffine_of_isAffineHom z₀
  let J := retainedProductInclusion b (f ≫ π) j
  let s₀ := productMarkedSection b π f zA j s Hmark
  let H₀ := productMarkedSection_isPullback b π f zA j s Hmark
  let J₁ := pullback.snd J (pullback.fst F w)
  let s₁ := baseChangeMarkedSection F J mZ s₀ H₀ w
  let h₁ := markedSection_baseChange_equation F J mZ s₀ H₀ w
  let H₁ := baseChangeMarkedSection_isPullback F J mZ s₀ H₀ w
  let R₁ := residualMarkedFiberMap gV J₁ z₀ s₁ h₁
  obtain ⟨v, hv⟩ := exists_chartResidualBoundary_factor b π f w j zA s Hmark d₁ bE hbE
  have hres := hscalar (R₁ ≫ k) (v ≫ coprod.inl) (by
    rw [Category.assoc, show k ≫ u₁ = pullback.fst F w from
      normQuotientBoundaryMap_fst F U w V.ι rfl]
    simpa only [Category.assoc, psiBoundaryInclusion, coprod.inl_desc] using hv)
  have hθ : (v ≫ coprod.inl).appTop θN = 1 := by
    rw [Hom.comp_appTop, CommRingCat.comp_apply, fullCorrectionCoordinate_infinity, map_one]
  rw [hθ, mul_one, Hom.comp_appTop, CommRingCat.comp_apply] at hres
  have hnorm := affineNorm_eq_marked_value gV J₁ z₀ s₁ h₁ H₁ (k.appTop r) hres
  rw [← normTop_eq_affineNorm gV,
    normTop_appTop_of_isPullback gU gV k V.ι (normQuotientBoundaryMap_isPullback F U w V.ι rfl)]
    at hnorm
  let m := correctionMarkBaseIso q π jA hA a z
  have hm : (s₁ ≫ J₁) ≫ pullback.fst F w = (αZ ≫ m.hom) ≫
      psiZeroInclusion q (f ≫ π) j p hB a z s hs := by
    calc
      _ = αZ ≫ s₀ ≫ J := by
        change (s₁ ≫ pullback.snd J (pullback.fst F w)) ≫ pullback.fst F w = _
        rw [Category.assoc, ← pullback.condition (f := J) (g := pullback.fst F w),
          ← Category.assoc, baseChangeMarkedSection_fst, Category.assoc]
      _ = _ := by
        rw [Category.assoc, correctionMarkToSourceProduct_map q π jA hA a f j p hB z s hs Hmark]
  have hmarkCoeff := hscalar ((s₁ ≫ J₁) ≫ k)
    ((αZ ≫ m.hom) ≫ coprod.inr) (by
      calc
        _ = (s₁ ≫ J₁) ≫ pullback.fst F w := by
          rw [Category.assoc, show k ≫ u₁ = pullback.fst F w from
            normQuotientBoundaryMap_fst F U w V.ι rfl]
        _ = _ := by
          simpa only [Category.assoc, psiBoundaryInclusion, coprod.inr_desc] using hm)
  have hθmark : ((αZ ≫ m.hom) ≫ coprod.inr).appTop θN = σ := by
    rw [Hom.comp_appTop, CommRingCat.comp_apply, fullCorrectionCoordinate_mark]
  rw [hθmark, Hom.comp_appTop, CommRingCat.comp_apply] at hmarkCoeff
  change (z₀).appTop (V.ι.appTop (normTop gU r)) * σ = 1
  rw [hnorm]
  exact hmarkCoeff

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

end

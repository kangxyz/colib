/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNegativeSign
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientNegativeLocalizationBoundary

/-!
# Original auxiliary negative classes preserve the intrinsic boundary

The actual current and original fine cone boundaries agree through the original
supported negative groups on the inverse-image and union support arrows. The
fine class maps retain their original finite-bottom comparisons, actual auxiliary
finite comparisons, and original fine inclusions. The integer-degree transport
is exactly the existing negative localization degree isomorphism. No boundary
or localization null is replaced or redefined.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
ParameterAuxiliaryNegativeBoundarySign.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open KTheory.Bass.SchemeNaturalSeed
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber
open GlobalSectionChangeIndex GlobalSupportedSection.ParameterAuxiliarySupport
  GlobalAuxiliaryParameterCoefficient

attribute [local instance] supportObject_compactSpace
  fiberNegativeFineClass_isIso openNegativeFineClass_isIso

private theorem stableHomotopyFunctor_obj (d : ℤ) (E : LoopPrespectrum.{u + 1}) :
    (stableHomotopyFunctor d).obj E = stableHomotopyGroup E d := rfl

private theorem inverse_class {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (q : B ⟶ D) (k : A ⟶ D) (h : e.hom ≫ q = k) :
    e.inv ≫ k = q := by
  rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

private theorem conjugate_boundary {C : Type*} [Category C]
    {A B D O V W : C} (e : A ≅ B) (a : O ⟶ V) (b : V ⟶ W)
    (c : W ⟶ B) (q : B ⟶ D) (k : A ⟶ D) (y : O ⟶ D) [IsIso k]
    (hs : e.hom ≫ q = k) (hδ : a ≫ b ≫ c ≫ q = y) :
    a ≫ b ≫ c ≫ e.inv = y ≫ inv k := by
  apply (cancel_mono k).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [inverse_class e q k hs]
  exact hδ

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

private theorem stable_degree_comparison
    (O S : LoopPrespectrum.{u + 1})
    (e : ∀ d : ℤ, stableHomotopyGroup O d ≅ stableHomotopyGroup S d)
    {d d' : ℤ} (h : d = d') :
    (eqToIso (congrArg stableHomotopyFunctor h)).hom.app O ≫ (e d').hom =
      (e d).hom ≫ (eqToIso (congrArg stableHomotopyFunctor h)).hom.app S := by
  subst d'
  change 𝟙 _ ≫ (e d).hom = (e d).hom ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

/-- The actual auxiliary negative boundary keeps the original open classes and degree cast. -/
@[reassoc]
theorem currentNegativeConnecting_fine (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    letI : CompactSpace (unionOpen f.left T) := unionOpen_compactSpace f T;
    letI : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T;
    letI : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f;
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison
        (supportArrow P (inverseOpen f.left T)) i).hom.app a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((currentTelescope (openAction f.left T)).obj (specUnder.obj a)) ≫
      currentConnecting f T a (-((i + 1 : ℕ) : ℤ)) ≫
      (currentFineSupportComparison f T a (-((i + 1 : ℕ) : ℤ))).hom =
    openNegativeFineClass f T i a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a) ≫
      boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (-((i + 1 : ℕ) : ℤ)) := by
  let : CompactSpace (unionOpen f.left T) := unionOpen_compactSpace f T
  let : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T
  let : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f
  have hd : (negativeLocalizationDegreeIso i).hom.app
        ((currentTelescope (openAction f.left T)).obj (specUnder.obj a)) ≫
      (currentFineOpenComparison f T a (-((i + 1 : ℕ) : ℤ) + 1)).hom =
    (currentFineOpenComparison f T a (-(i : ℤ))).hom ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a) :=
    stable_degree_comparison _ _ (currentFineOpenComparison f T a)
      (d := -(i : ℤ)) (d' := -((i + 1 : ℕ) : ℤ) + 1) (by omega)
  rw [current_fine_connecting f T a (-((i + 1 : ℕ) : ℤ)), ← Category.assoc _ _
    (boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (-((i + 1 : ℕ) : ℤ))), hd]
  simp only [← Category.assoc]
  rw [currentNegativeKComparison_fine_open f T i a]

/-- The unchanged intrinsic and original cone boundaries induce the same map on every original
auxiliary-supported negative group, including the exact original integer-degree cast. -/
theorem currentNegativeConnecting_eq_original (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    letI : CompactSpace (unionOpen f.left T) := unionOpen_compactSpace f T;
    letI : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T;
    letI : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f;
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison
        (supportArrow P (inverseOpen f.left T)) i).hom.app a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((currentTelescope (openAction f.left T)).obj (specUnder.obj a)) ≫
      currentConnecting f T a (-((i + 1 : ℕ) : ℤ)) ≫
      (GlobalSupportedParameterCoefficient.currentNegativeKComparison
        (supportArrow Q (unionOpen f.left T)) (i + 1)).inv.app a =
    openNegativeFineClass f T i a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a) ≫
      boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (-((i + 1 : ℕ) : ℤ)) ≫
      inv (fiberNegativeFineClass f T (i + 1) a) := by
  let : CompactSpace (unionOpen f.left T) := unionOpen_compactSpace f T
  let : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T
  let : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f
  let e := (GlobalSupportedParameterCoefficient.currentNegativeKComparison
    (supportArrow Q (unionOpen f.left T)) (i + 1)).app a
  have hs := currentNegativeKComparison_fine_fiber f T (i + 1) a
  have hδ := currentNegativeConnecting_fine f T i a
  dsimp only [Functor.comp_obj, stableHomotopyFunctor_obj, fiber, fiberAction,
    GlobalSupportedSection.ParameterAuxiliarySupport.openModel, openAction, supportArrow,
    Over.homMk_left] at e hs hδ ⊢
  have hr := conjugate_boundary e _ _ _ _ _ _ hs hδ
  exact hr

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber

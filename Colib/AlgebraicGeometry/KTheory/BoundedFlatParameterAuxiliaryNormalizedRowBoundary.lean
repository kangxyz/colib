/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowClasses
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowBoundaryComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientNegativeLocalizationBoundary

/-!
# The normalized row's intrinsic boundary on every original negative group

The actual row boundary first satisfies the signed same-null comparison with
the unchanged fine boundary. The independent finite negative-class maps then
identify its action on the original groups. Both integer-degree transports are
the existing negative localization degree isomorphism. No boundary is defined
by conjugating a previously supplied group homomorphism.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
ParameterAuxiliaryNormalizedRowBoundary.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization
open GlobalSectionChangeIndex GlobalSupportedSection.ParameterAuxiliarySupport
  ParameterAuxiliaryCurrentFiber
open GlobalAuxiliaryParameterCoefficient
attribute [local instance] supportObject_compactSpace
attribute [local instance] GlobalSupportedParameterCoefficient.normalizedRowNegativeClass_isIso
attribute [local instance] fiberNegativeFineClass_isIso
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

private theorem degree_comparison (O S : LoopPrespectrum.{u + 1})
    (e : ∀ d : ℤ, stableHomotopyGroup O d ≅ stableHomotopyGroup S d)
    {d d' : ℤ} (h : d = d') :
    (eqToIso (congrArg stableHomotopyFunctor h)).hom.app O ≫ (e d').hom =
      (e d).hom ≫ (eqToIso (congrArg stableHomotopyFunctor h)).hom.app S := by
  subst d'
  change 𝟙 _ ≫ (e d).hom = (e d).hom ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

private theorem degree_boundary {C : Type*} [Category C]
    {A B D E F G : C} (c : A ⟶ B) (δ : B ⟶ D) (e : D ⟶ E)
    (v : B ⟶ F) (w : A ⟶ G) (c' : G ⟶ F) (δ' : F ⟶ E)
    (hδ : δ ≫ e = v ≫ δ') (hc : c ≫ v = w ≫ c') :
    (c ≫ δ) ≫ e = w ≫ (c' ≫ δ') := by
  rw [Category.assoc, hδ, ← Category.assoc, hc, Category.assoc]

private theorem boundary_on_classes {C : Type*} [Category C]
    {A B S T U V : C} (nO : A ⟶ S) (nS : B ⟶ T) [IsIso nS]
    (fO : A ⟶ U) (fS : B ⟶ V) [IsIso fS]
    (eO : S ⟶ U) (eS : T ⟶ V) (δn : S ⟶ T) (δf : U ⟶ V)
    (hO : nO ≫ eO = fO) (hS : nS ≫ eS = fS)
    (hδ : δn ≫ eS = eO ≫ δf) :
    nO ≫ δn ≫ inv nS = fO ≫ δf ≫ inv fS := by
  apply (cancel_mono fS).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hS, IsIso.inv_hom_id_assoc, hδ, ← Category.assoc, hO]

/-- Every original auxiliary negative boundary retains both original class maps and degree casts.
-/
theorem normalizedNegativeConnecting_eq_original (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    letI : CompactSpace (unionOpen f.left T) := unionOpen_compactSpace f T;
    letI : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T;
    letI : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f;
    GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
        (supportArrow P (inverseOpen f.left T)) i a ≫
      (negativeLocalizationDegreeIso i).hom.app
        (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
          (specUnder.obj a)) ≫
      normalizedPresentationConnecting f T a (-((i + 1 : ℕ) : ℤ)) ≫
      inv (GlobalSupportedParameterCoefficient.normalizedRowNegativeClass
        (supportArrow Q (unionOpen f.left T)) (i + 1) a) =
    openNegativeFineClass f T i a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a) ≫
      boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (-((i + 1 : ℕ) : ℤ)) ≫
      inv (fiberNegativeFineClass f T (i + 1) a) := by
  let := unionOpen_compactSpace f T
  let := inverseOpen_compactSpace f T
  let := open_quasiSeparatedSpace f
  have hd := degree_comparison _ _ (normalizedFineOpenComparison f T a)
    (d := -(i : ℤ)) (d' := -((i + 1 : ℕ) : ℤ) + 1) (by omega)
  have hδ : ((negativeLocalizationDegreeIso i).hom.app
        (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
          (specUnder.obj a)) ≫
      normalizedPresentationConnecting f T a (-((i + 1 : ℕ) : ℤ))) ≫
        (normalizedFineSupportComparison f T a (-((i + 1 : ℕ) : ℤ))).hom =
      (normalizedFineOpenComparison f T a (-(i : ℤ))).hom ≫
        ((negativeLocalizationDegreeIso i).hom.app
          ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a) ≫
          boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a
            (-((i + 1 : ℕ) : ℤ))) := by
    exact degree_boundary _ _ _ _ _ _ _
      (normalizedPresentationConnecting_fine f T a (-((i + 1 : ℕ) : ℤ))) hd
  simpa only [Category.assoc] using boundary_on_classes _ _ _ _ _ _ _ _
    (normalizedNegativeClass_fine_open f T i a)
    (normalizedNegativeClass_fine_fiber f T (i + 1) a) hδ

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization

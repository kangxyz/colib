/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowPerfectClasses
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNegativeSign

/-!
# Every original negative auxiliary class in the actual normalized row

The independent finite normalized-row classes agree with the original fine
classes on the union, auxiliary, and inverse-open support arrows. The proofs
consume the actual all-negative correction identities and retain the original
finite comparisons and inclusions.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
ParameterAuxiliaryNormalizedRowClasses.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization
open GlobalSectionChangeIndex GlobalSupportedSection.ParameterAuxiliarySupport
  ParameterAuxiliaryCurrentFiber
open GlobalAuxiliaryParameterCoefficient
attribute [local instance] supportObject_compactSpace
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

private theorem stableHomotopyFunctor_obj (d : ℤ) (E : LoopPrespectrum.{u + 1}) :
    (stableHomotopyFunctor d).obj E = stableHomotopyGroup E d := rfl

private theorem class_triangle {A B C D : AddCommGrpCat.{u + 1}}
    (g : A ⟶ B) (s : B ⟶ C) (e : C ⟶ D) (v : B ⟶ D)
    (k : A ⟶ C) (w : A ⟶ D) (hk : g ≫ s = k)
    (he : s ≫ e = v) (hw : g ≫ v = w) : k ≫ e = w := by
  rw [← hk, Category.assoc, he, hw]

/-- The original fiber negative classes through the independent normalized finite inclusion. -/
@[reassoc]
theorem normalizedNegativeClass_fine_fiber (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    GlobalSupportedParameterCoefficient.normalizedRowNegativeClass (supportArrow Q (unionOpen
      f.left T)) i a ≫
        (normalizedFineSupportComparison f T a (-(i : ℤ))).hom =
      fiberNegativeFineClass f T i a := by
  let := unionOpen_compactSpace f T
  exact class_triangle
    ((GlobalSupportedParameterCoefficient.currentNegativeKComparison
      (supportArrow Q (unionOpen f.left T)) i).hom.app a)
    ((stableHomotopyFunctor (-(i : ℤ))).map (normalizedFiberPresentationComparison f.left T
      (specUnder.obj a)))
    (normalizedFineSupportComparison f T a (-(i : ℤ))).hom
    (currentFineSupportComparison f T a (-(i : ℤ))).hom
    _ _ (GlobalSupportedParameterCoefficient.currentNegativeKComparison_normalizedRow
      (supportArrow Q (unionOpen f.left T)) i a)
    (normalizedFineSupportComparison_triangle f T a (-(i : ℤ)))
    (currentNegativeKComparison_fine_fiber f T i a)

omit [IsOpenImmersion f.left] [CompactSpace P.left] in
/-- The original ambient negative classes through the independent normalized finite inclusion. -/
@[reassoc]
theorem normalizedNegativeClass_fine_ambient (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    GlobalSupportedParameterCoefficient.normalizedRowNegativeClass (supportArrow Q T) i a ≫
        (normalizedFineAmbientComparison T a (-(i : ℤ))).hom =
      ambientNegativeFineClass T i a := by
  exact class_triangle
    ((GlobalSupportedParameterCoefficient.currentNegativeKComparison (supportArrow Q T)
      i).hom.app a)
    ((stableHomotopyFunctor (-(i : ℤ))).map (normalizedAmbientPresentationComparison T
      (specUnder.obj a)))
    (normalizedFineAmbientComparison T a (-(i : ℤ))).hom
    (currentFineAmbientComparison T a (-(i : ℤ))).hom
    _ _ (GlobalSupportedParameterCoefficient.currentNegativeKComparison_normalizedRow
      (supportArrow Q T) i a)
    (normalizedFineAmbientComparison_triangle T a (-(i : ℤ)))
    (by
      simp only [currentFineAmbientComparison, Iso.trans_hom]
      have h := currentNegativeKComparison_fine_ambient T i a
      dsimp only [Functor.comp_obj, stableHomotopyFunctor_obj, ambient, ambientAction,
        supportArrow, Over.homMk_left, asIso] at h ⊢
      exact h)

omit [CompactSpace Q.left] in
/-- The original open negative classes through the independent normalized finite inclusion. -/
@[reassoc]
theorem normalizedNegativeClass_fine_open (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    GlobalSupportedParameterCoefficient.normalizedRowNegativeClass (supportArrow P (inverseOpen
      f.left T)) i a ≫
        (normalizedFineOpenComparison f T a (-(i : ℤ))).hom =
      openNegativeFineClass f T i a := by
  let := inverseOpen_compactSpace f T
  let := open_quasiSeparatedSpace f
  exact class_triangle
    ((GlobalSupportedParameterCoefficient.currentNegativeKComparison
      (supportArrow P (inverseOpen f.left T)) i).hom.app a)
    ((stableHomotopyFunctor (-(i : ℤ))).map (normalizedOpenPresentationComparison f.left T
      (specUnder.obj a)))
    (normalizedFineOpenComparison f T a (-(i : ℤ))).hom
    (currentFineOpenComparison f T a (-(i : ℤ))).hom
    _ _ (GlobalSupportedParameterCoefficient.currentNegativeKComparison_normalizedRow
      (supportArrow P (inverseOpen f.left T)) i a)
    (normalizedFineOpenComparison_triangle f T a (-(i : ℤ)))
    (currentNegativeKComparison_fine_open f T i a)

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowPerfectClasses

/-!
# The actual normalized row boundary and the original fine boundary

The actual whole-null comparison identifies the intrinsic row connecting map
with the original fine cone boundary in every integer degree. This comparison
is independent of the subsequent original negative-class identifications.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
ParameterAuxiliaryNormalizedRowBoundaryComparison.lean`, revision
  `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization
open GlobalSectionChangeIndex GlobalSupportedSection.ParameterAuxiliarySupport
  ParameterAuxiliaryCurrentFiber
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

private theorem boundary_triangle {C : Type*} [Category C]
    {A B D A' B' D' : C} (s : A ⟶ B) [Epi s] (t : A' ⟶ B')
    (e : B ⟶ D) (e' : B' ⟶ D') (v : A ⟶ D) (v' : A' ⟶ D')
    (δ : A ⟶ A') (δ' : B ⟶ B') (δ'' : D ⟶ D')
    (hs : s ≫ e = v) (ht : t ≫ e' = v')
    (hr : δ ≫ t = s ≫ δ') (hf : δ ≫ v' = v ≫ δ'') :
    δ' ≫ e' = e ≫ δ'' := by
  apply (cancel_epi s).1
  rw [← Category.assoc, ← hr, Category.assoc, ht, hf,
    ← hs, Category.assoc]

/-- The normalized row's own signed boundary agrees with the original fine cone boundary. -/
@[reassoc]
theorem normalizedPresentationConnecting_fine
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    normalizedPresentationConnecting f T a d ≫
        (normalizedFineSupportComparison f T a d).hom =
      (normalizedFineOpenComparison f T a (d + 1)).hom ≫
        boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d := by
  have : IsIso ((stableHomotopyFunctor (d + 1)).map
      (normalizedOpenPresentationComparison f.left T (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.supportedComparison_stable
      (inverseOpen f.left T).ι (specUnder.obj a) (d + 1)
  have : Epi ((stableHomotopyFunctor (d + 1)).map
      (normalizedOpenPresentationComparison f.left T (specUnder.obj a))) := inferInstance
  exact boundary_triangle
    ((stableHomotopyFunctor (d + 1)).map
      (normalizedOpenPresentationComparison f.left T (specUnder.obj a)))
    ((stableHomotopyFunctor d).map
      (normalizedFiberPresentationComparison f.left T (specUnder.obj a)))
    _ _ _ _ _ _ _
    (normalizedFineOpenComparison_triangle f T a (d + 1))
    (normalizedFineSupportComparison_triangle f T a d)
    (current_normalizedPresentation_connecting f T a d)
    (current_fine_connecting f T a d)

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization

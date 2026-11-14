/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterSupportedNormalizedRowClasses
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowConnecting
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryPerfectClasses

/-!
# Original nonnegative auxiliary classes in the actual normalized row

The three normalized-to-fine comparisons use the actual current-to-normalized
maps and the existing current-to-fine isomorphisms. The normalized classes
are independently defined by their finite row inclusions. Their equations
retain the original perfect classes in every nonnegative degree, including
zero. Negative original-group comparisons are supplied by a separate consumer.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
ParameterAuxiliaryNormalizedRowPerfectClasses.lean`, revision
  `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory

universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization
open GlobalSectionChangeIndex GlobalSupportedSection.ParameterAuxiliarySupport
  ParameterAuxiliaryCurrentFiber
open GlobalAuxiliaryParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

private theorem comparison_triangle {C : Type*} [Category C]
    {A B D : C} (s : A ⟶ B) [IsIso s] (v : A ≅ D) :
    s ≫ ((asIso s).symm ≪≫ v).hom = v.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, ← Category.assoc,
    IsIso.hom_inv_id, Category.id_comp]

omit [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
  [CompactSpace T] in
/-- The actual normalized fiber row compares with the unchanged fine object. -/
def normalizedFineSupportComparison
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup
      (ParameterTensorNormalizedRowPresentation.supported (unionOpen f.left T).ι (specUnder.obj
        a)) d ≅
      stableHomotopyGroup ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj
        a) d := by
  have : IsIso ((stableHomotopyFunctor d).map (normalizedFiberPresentationComparison f.left T
    (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.supportedComparison_stable
      (unionOpen f.left T).ι (specUnder.obj a) d
  exact (asIso ((stableHomotopyFunctor d).map
    (normalizedFiberPresentationComparison f.left T (specUnder.obj a)))).symm ≪≫
      currentFineSupportComparison f T a d

omit [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
  [CompactSpace T] in
/-- The fiber comparison retains both original routes as actual morphisms. -/
@[reassoc]
theorem normalizedFineSupportComparison_triangle
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (stableHomotopyFunctor d).map (normalizedFiberPresentationComparison f.left T
      (specUnder.obj a)) ≫
        (normalizedFineSupportComparison f T a d).hom =
      (currentFineSupportComparison f T a d).hom := by
  have : IsIso ((stableHomotopyFunctor d).map (normalizedFiberPresentationComparison f.left T
    (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.supportedComparison_stable
      (unionOpen f.left T).ι (specUnder.obj a) d
  exact comparison_triangle _ _

omit [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- The actual normalized ambient row compares with the unchanged fine object. -/
def normalizedFineAmbientComparison
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup
      (ParameterTensorNormalizedRowPresentation.supported (T).ι (specUnder.obj a)) d ≅
      stableHomotopyGroup ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFunctor T).obj
        a) d := by
  have : IsIso ((stableHomotopyFunctor d).map (normalizedAmbientPresentationComparison T
    (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.supportedComparison_stable
      (T).ι (specUnder.obj a) d
  exact (asIso ((stableHomotopyFunctor d).map
    (normalizedAmbientPresentationComparison T (specUnder.obj a)))).symm ≪≫
      currentFineAmbientComparison T a d

omit [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- The ambient comparison retains both original routes as actual morphisms. -/
@[reassoc]
theorem normalizedFineAmbientComparison_triangle
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (stableHomotopyFunctor d).map (normalizedAmbientPresentationComparison T (specUnder.obj a)) ≫
        (normalizedFineAmbientComparison T a d).hom =
      (currentFineAmbientComparison T a d).hom := by
  have : IsIso ((stableHomotopyFunctor d).map (normalizedAmbientPresentationComparison T
    (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.supportedComparison_stable
      (T).ι (specUnder.obj a) d
  exact comparison_triangle _ _

omit [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- The actual normalized open row compares with the unchanged fine object. -/
def normalizedFineOpenComparison
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup
      (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
        (specUnder.obj a)) d ≅
      stableHomotopyGroup ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f
        T).obj a) d := by
  have : IsIso ((stableHomotopyFunctor d).map (normalizedOpenPresentationComparison f.left T
    (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.supportedComparison_stable
      (inverseOpen f.left T).ι (specUnder.obj a) d
  exact (asIso ((stableHomotopyFunctor d).map
    (normalizedOpenPresentationComparison f.left T (specUnder.obj a)))).symm ≪≫
      currentFineOpenComparison f T a d

omit [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- The open comparison retains both original routes as actual morphisms. -/
@[reassoc]
theorem normalizedFineOpenComparison_triangle
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (stableHomotopyFunctor d).map (normalizedOpenPresentationComparison f.left T (specUnder.obj
      a)) ≫
        (normalizedFineOpenComparison f T a d).hom =
      (currentFineOpenComparison f T a d).hom := by
  have : IsIso ((stableHomotopyFunctor d).map (normalizedOpenPresentationComparison f.left T
    (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.supportedComparison_stable
      (inverseOpen f.left T).ι (specUnder.obj a) d
  exact comparison_triangle _ _

omit [CompactSpace P.left] [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- Every original fiber perfect class, including degree zero, has the prescribed row image. -/
theorem normalized_fine_fiber_perfectClass
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((fiber f.left T).obj (specUnder.obj a)).obj.waldhausen.K n) :
    (normalizedFineSupportComparison f T a (n : ℤ)).hom
      (SchemeModelRowSeed.normalizedModelClass (fiber f.left T)
        (ParameterLaurentTrack.supportedUnit (unionOpen f.left T).ι)
        (ParameterLaurentTrack.supportedUnit_naturality (unionOpen f.left T).ι)
        (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (auxiliaryFiberPerfectStableEquiv f T a n (Additive.ofMul (auxiliaryFiberPerfectKEquiv
          f T a n
          (CategoryTheory.Waldhausen.KMap ((fiberComparison f T).app a).hom.isExact n x)))) := by
  have hc := SchemeModelRowSeed.normalizedComparison_modelClass (fiber f.left T)
    (ParameterLaurentTrack.supportedUnit (unionOpen f.left T).ι)
    (ParameterLaurentTrack.supportedUnit_naturality (unionOpen f.left T).ι)
    (specUnder.obj a) n x
  have ht := ConcreteCategory.congr_hom
    (normalizedFineSupportComparison_triangle f T a (n : ℤ))
    (SchemeNaturalSeed.currentModelClass (fiber f.left T) (fiberAction f.left T) (specUnder.obj
      a) n x)
  exact (congrArg (normalizedFineSupportComparison f T a (n : ℤ)).hom hc).symm.trans
    (ht.trans (current_fine_fiber_perfectClass f T a n x))

omit [IsOpenImmersion f.left] [CompactSpace P.left] [QuasiSeparatedSpace Q.left]
  [CompactSpace T] in
/-- Every original ambient perfect class, including degree zero, has the prescribed row image. -/
theorem normalized_fine_ambient_perfectClass
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ambient T).obj (specUnder.obj a)).obj.waldhausen.K n) :
    (normalizedFineAmbientComparison T a (n : ℤ)).hom
      (SchemeModelRowSeed.normalizedModelClass (ambient T)
        (ParameterLaurentTrack.supportedUnit (T).ι)
        (ParameterLaurentTrack.supportedUnit_naturality (T).ι)
        (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a)
        (auxiliaryAmbientPerfectStableEquiv T a n (Additive.ofMul
          (auxiliaryAmbientPerfectKEquiv T a n
          (CategoryTheory.Waldhausen.KMap ((ambientComparison Q T).app a).hom.isExact n x)))) := by
  have hc := SchemeModelRowSeed.normalizedComparison_modelClass (ambient T)
    (ParameterLaurentTrack.supportedUnit (T).ι)
    (ParameterLaurentTrack.supportedUnit_naturality (T).ι)
    (specUnder.obj a) n x
  have ht := ConcreteCategory.congr_hom
    (normalizedFineAmbientComparison_triangle T a (n : ℤ))
    (SchemeNaturalSeed.currentModelClass (ambient T) (ambientAction T) (specUnder.obj a) n x)
  exact (congrArg (normalizedFineAmbientComparison T a (n : ℤ)).hom hc).symm.trans
    (ht.trans (current_fine_ambient_perfectClass T a n x))

omit [IsOpenImmersion f.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
  [CompactSpace T] in
/-- Every original open perfect class, including degree zero, has the prescribed row image. -/
theorem normalized_fine_open_perfectClass
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((openModel f.left T).obj (specUnder.obj a)).obj.waldhausen.K n) :
    (normalizedFineOpenComparison f T a (n : ℤ)).hom
      (SchemeModelRowSeed.normalizedModelClass (openModel f.left T)
        (ParameterLaurentTrack.supportedUnit (inverseOpen f.left T).ι)
        (ParameterLaurentTrack.supportedUnit_naturality (inverseOpen f.left T).ι)
        (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
        (auxiliaryOpenPerfectStableEquiv f T a n (Additive.ofMul (auxiliaryOpenPerfectKEquiv f T a n
          (CategoryTheory.Waldhausen.KMap ((openComparison f T).app a).hom.isExact n x)))) := by
  have hc := SchemeModelRowSeed.normalizedComparison_modelClass (openModel f.left T)
    (ParameterLaurentTrack.supportedUnit (inverseOpen f.left T).ι)
    (ParameterLaurentTrack.supportedUnit_naturality (inverseOpen f.left T).ι)
    (specUnder.obj a) n x
  have ht := ConcreteCategory.congr_hom
    (normalizedFineOpenComparison_triangle f T a (n : ℤ))
    (SchemeNaturalSeed.currentModelClass (openModel f.left T) (openAction f.left T)
      (specUnder.obj a) n x)
  exact (congrArg (normalizedFineOpenComparison f T a (n : ℤ)).hom hc).symm.trans
    (ht.trans (current_fine_open_perfectClass f T a n x))

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryNormalizedRowLocalization

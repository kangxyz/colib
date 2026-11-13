/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFineTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIteratedFullNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationTelescopeSquares
public import Colib.KTheory.Bass.StrictDiagramIndexRowTelescopeNaturality

/-!
# The complete supported forgetful square on the actual Spec-row telescopes

The original supported inclusion is preserved by the actual Model row isomorphism, every
finite index comparison, and the entire quotient telescope. Composing with the existing
coefficient restrictions retains the literal original fine supported-to-ambient arrow.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection ParameterLaurentTrack
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- Realization preserves the full original supported-to-ambient row square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterTelescopeForget.lean:37"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem spectrum_forget_square :
    Functor.whiskerLeft specUnder
        (Functor.whiskerRight (ParameterModels.forget f.left) prespectrumFunctor) ≫
      (GlobalParameterCoefficient.rowSpectrumIso Q).hom =
    (rowSpectrumIso f).hom ≫ Functor.whiskerRight (supportedRowForget f) prespectrumFunctor := by
  have h := congrArg (fun η => Functor.whiskerRight η prespectrumFunctor)
    (parameterSupportedRowIso_forget f).symm
  simp only [Functor.whiskerRight_comp] at h
  apply NatTrans.ext
  funext a
  exact congrArg (fun η => η.app a) h

/-- The actual original supported inclusion commutes at every finite Spec-row stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterTelescopeForget.lean:50"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem finite_forget_square (i : ℕ) :
    Functor.whiskerLeft specUnder ((strictDiagramIterate squareFunctor i).map
        (Functor.whiskerRight (ParameterModels.forget f.left) prespectrumFunctor)) ≫
      (GlobalParameterCoefficient.finiteIso Q i).hom =
    (finiteIso f i).hom ≫ LocalizationTelescope.finiteForget f i :=
  StrictDiagramIndexRow.finiteIso_naturality specUnder
    (laurentUnderSquareFunctor (CommRingCat.of (ULift.{u} ℤ))) squareFunctor specSquare
    (rowSpectrumIso f) (GlobalParameterCoefficient.rowSpectrumIso Q)
    (Functor.whiskerRight (ParameterModels.forget f.left) prespectrumFunctor)
    (Functor.whiskerRight (supportedRowForget f) prespectrumFunctor)
    (spectrum_forget_square f) i

/-- The complete original supported inclusion square holds on the actual quotient telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterTelescopeForget.lean:63"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem telescope_forget_square :
    Functor.whiskerLeft specUnder (ParameterFullCurrentNull.iteratedForget f.left) ≫
        (GlobalParameterCoefficient.telescopeIso Q).hom =
      (telescopeIso f).hom ≫ LocalizationTelescope.forget f := by
  exact StrictDiagramIndexRow.telescopeMap_naturality specUnder
    (laurentUnderSquareFunctor (CommRingCat.of (ULift.{u} ℤ))) squareFunctor specSquare
    (rowSpectrumIso f) (GlobalParameterCoefficient.rowSpectrumIso Q)
    (Functor.whiskerRight (ParameterModels.forget f.left) prespectrumFunctor)
    (Functor.whiskerRight (supportedRowForget f) prespectrumFunctor)
    (spectrum_forget_square f)
    (KTheory.Bass.SchemeNaturalSeed.seed (supportedTrack f.left))
    (KTheory.Bass.SchemeNaturalSeed.seed (ambientTrack Q.left))
    (supportedLaurentAction f).track.seed (globalLaurentAction Q).track.seed
    (KTheory.Bass.SchemeNaturalSeed.seed_square _ _ _ (forget_equivariant f.left))
    (supportedRowForget_seed f) (seed_square_row f)
    (GlobalParameterCoefficient.seed_square_row Q)

/-- Both actual fine comparisons retain the original fine supported forgetful arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterTelescopeForget.lean:81"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem fineTelescope_forget_square :
    Functor.whiskerLeft specUnder (ParameterFullCurrentNull.iteratedForget f.left) ≫
        GlobalParameterCoefficient.fineTelescopeComparison Q =
      fineTelescopeComparison f ≫ boundedAboveFlatCoefficientSupportedBassTelescopeForget f := by
  change _ ≫ ((GlobalParameterCoefficient.telescopeIso Q).hom ≫ telescopeRestriction Q) =
    ((telescopeIso f).hom ≫ SupportedTelescope.telescopeRestriction f) ≫ _
  rw [← Category.assoc, telescope_forget_square, Category.assoc,
    ← LocalizationTelescope.forget_square, ← Category.assoc]

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient


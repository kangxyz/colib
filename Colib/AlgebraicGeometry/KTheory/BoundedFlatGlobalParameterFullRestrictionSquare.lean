/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFullRestrictionTelescope
public import Colib.KTheory.Bass.StrictDiagramIndexRowNaturality

/-! # The actual full-open Spec comparison at every finite stage -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The full Model square realizes to the same spectrum row square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFullRestrictionSquare.lean:28"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem fullRestriction_spectrum_square :
    Functor.whiskerLeft specUnder (parameterRestrictionMap f) ≫ (rowSpectrumIso P).hom =
      (rowSpectrumIso Q).hom ≫
        Functor.whiskerRight (globalOpenFineRestriction f) prespectrumFunctor := by
  have h := congrArg (fun η => Functor.whiskerRight η prespectrumFunctor)
    (fullRestriction_model_square f)
  simp only [Functor.whiskerRight_comp] at h
  apply NatTrans.ext
  funext a
  exact congrArg (fun η => η.app a) h

/-- All finite stages retain the actual original change-weak/full-open factorization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFullRestrictionSquare.lean:40"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem fullRestriction_finite_square (i : ℕ) :
    Functor.whiskerLeft specUnder (parameterFiniteRestriction f i) ≫ (finiteIso P i).hom =
      (finiteIso Q i).hom ≫ LocalizationTelescope.finiteOpen f i ≫
        FullOpenTelescope.finiteRestriction f i := by
  have h := StrictDiagramIndexRow.finiteIso_naturality specUnder
    (laurentUnderSquareFunctor (CommRingCat.of (ULift.{u} ℤ))) squareFunctor specSquare
    (rowSpectrumIso Q) (rowSpectrumIso P) (parameterRestrictionMap f)
    (Functor.whiskerRight (globalOpenFineRestriction f) prespectrumFunctor)
    (fullRestriction_spectrum_square f) i
  have hm := congrArg (fun η => Functor.whiskerRight η prespectrumFunctor)
    (globalFullRestriction_factor f)
  simp only [Functor.whiskerRight_comp] at hm
  have hf := congrArg
    ((strictDiagramIterate (laurentUnderSquareFunctor (CommRingCat.of (ULift.{u} ℤ))) i).map)
    hm
  rw [CategoryTheory.Functor.map_comp] at hf
  exact h.trans (congrArg (fun z => (finiteIso Q i).hom ≫ z) hf.symm)

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient


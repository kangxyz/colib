/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawPastedCells
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawChartProductWhole
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCubeExtension

/-!
# The whole raw input homotopy on the evaluated strict cylinder

The three attached compact surfaces recover the actual raw input homotopy after the original
span evaluation. All three height cells, their shared boundaries, and the independent raw
homotopy time are retained as an equality of continuous maps at every prespectrum level.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawPastedNative
open GlobalSectionChangeIndex Path.CarrierHalfPaths InputRawPastedParameter
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The entire compact surface is exactly the original raw homotopy on span evaluation. -/
theorem whole_native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (parameter g) n = nativeFamily g n := by
  apply ContinuousMap.ext
  rintro ⟨⟨r, s⟩, x⟩
  rcases three_cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact (CommonReferenceNerve.compactFamily_of_point_eq
      (InputMixedDesc.sourceMap g) (parameter g)
      (InputRawChartProductNodes.parameter g plus GlobalRawBass.plus_projection)
      (r, lower t) (t, r) (parameter_lower g r t) n x).trans
      ((DFunLike.congr_fun (InputRawChartProductNative.whole_native g plus
        GlobalRawBass.plus_projection n) ((t, r), x)).trans (native_lower g n r t x).symm)
  · exact (CommonReferenceNerve.compactFamily_of_point_eq
      (InputMixedDesc.sourceMap g) (parameter g) (InputRawDesc.parameter g)
      (r, upper (lower t)) (r, t) (parameter_middle g r t) n x).trans
      ((InputRawDesc.parameter_native g n r t x).trans
        (native_middle g n r t x).symm)
  · exact (CommonReferenceNerve.compactFamily_of_point_eq
      (InputMixedDesc.sourceMap g) (parameter g)
      (InputRawChartProductNodes.parameter g minus GlobalRawBass.minus_projection)
      (r, upper (upper t)) (unitInterval.symm t, r) (parameter_upper g r t) n x).trans
      ((DFunLike.congr_fun (InputRawChartProductNative.whole_native g minus
        GlobalRawBass.minus_projection n) ((unitInterval.symm t, r), x)).trans
          (native_upper g n r t x).symm)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawPastedNative

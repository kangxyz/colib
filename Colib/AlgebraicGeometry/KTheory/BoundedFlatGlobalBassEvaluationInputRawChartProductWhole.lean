/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawChartProductNodes

/-!
# The whole attached raw evaluation-square family

The compact evaluator of the reanchored ten-node parameter is the entire original two-time
raw square acting on the moving projection-evaluation input. The proof transports the whole
finite-simplex family and then uses the original product's continuous-map equality.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawChartProductNative
open GlobalSectionChangeIndex InputRawChartProductNodes
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The entire compact family is unchanged by its actual mixed-reference transport. -/
theorem product_family (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (parameter g k hk) n =
    InputRawSquareProduct.nativeFamily (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g) (projection.app Y) n := by
  have h := congrArg (fun S => prespectrumSimplexFamily S n) (product_simplex g k hk)
  apply ContinuousMap.ext
  intro z
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (InputMixedDesc.sourceMap g) (parameter g k hk) (nodes g k hk) z.1
    (InputRawSquareProduct.parameter z.1) rfl n z.2).trans
    (DFunLike.congr_fun h (InputRawSquareProduct.parameter z.1, z.2))

/-- The whole original raw square acts on the actual moving projection-evaluation input. -/
theorem whole_native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (parameter g k hk) n =
    ((boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g)).level n).comp
        (InputRawSquareProduct.movingParameter (projection.app Y) n) :=
  (product_family g k hk n).trans
    (InputRawSquareProduct.whole_native (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g) (projection.app Y) n)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputRawChartProductNative

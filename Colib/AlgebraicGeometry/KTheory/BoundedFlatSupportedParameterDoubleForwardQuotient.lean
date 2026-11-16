/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedParameterSpecDoubleUnitTransport
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeDoubleContractionSwap

/-!
# The original supported double positive comparison on parameter schemes

The two unchanged supported parameter tracks followed by the two actual quotient
projections are natural on the qc parameter row. At each actual integral Spec
fiber the comparison is invertible by the original supported coefficient α₀ and
α₁. The full supported row comparison and both Laurent Spec maps are retained.
The actual descended Laurent swap has the resulting degree-two quotient sign.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
SupportedParameterDoubleForwardQuotient.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.TwoChart
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedParameterCoefficientUnitOperation
open GlobalSupportedSection GlobalSectionChangeIndex SupportedParameterSpecQuotientTransport
attribute [local irreducible] ParameterModels.supported
  boundedAboveFlatCoefficientSupportedModelFunctor ParameterLaurentTrack.supportedTrack
  boundedAboveFlatCoefficientSupportedLaurentAction
local notation "R" => CommRingCat.of (ULift ℤ)
local notation "p" => NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus
local notation "m" => NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus
local notation "L" => AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.op

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original supported one-unit operation is natural on the actual qc parameter row. -/
def parameterUnitSection (d : ℤ) : quasiCompactStableFunctor f d ⟶
    L ⋙ quasiCompactStableFunctor f (d + 1) where
  app X := ((ParameterLaurentTrack.supportedTrack f).homotopy
    (op X.unop.obj)).stableOperation d
  naturality {X Y} g := parameterOperation_naturality f
    (X := op X.unop.obj) (Y := op Y.unop.obj)
    (quasiCompactSchemesInclusion.op.map g) d

/-- The two original supported parameter operations form a natural transformation. -/
def doubleUnitSection : quasiCompactStableFunctor f 0 ⟶
    L ⋙ L ⋙ quasiCompactStableFunctor f 2 :=
  parameterUnitSection f 0 ≫ Functor.whiskerLeft L (parameterUnitSection f 1)

/-- The natural twice-positive supported comparison uses both original quotient projections. -/
def doubleForwardQuotient : quasiCompactStableFunctor f 0 ⟶
    contraction p m (contraction p m (quasiCompactStableFunctor f 2)) where
  app X := (doubleUnitSection f).app X ≫
    doubleContractionπ p m (quasiCompactStableFunctor f 2) X
  naturality {X Y} g := by
    rw [← Category.assoc, (doubleUnitSection f).naturality, Category.assoc]
    simp only [Functor.comp_map]
    rw [doubleContractionπ_naturality, ← Category.assoc]

/-- The actual descended swap has the sign of the unchanged supported double-unit operation. -/
theorem doubleForwardQuotient_swap (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (doubleForwardQuotient f).app X ≫
        PolynomialLaurent.Relative.doubleContractionSwap (quasiCompactStableFunctor f 2) X =
      -(doubleForwardQuotient f).app X := by
  change (SupportedParameterDoubleUnit.doubleUnit f (op X.unop.obj) ≫ _) ≫ _ = -(_ ≫ _)
  rw [Category.assoc, PolynomialLaurent.Relative.doubleContractionπ_swap,
    ← Category.assoc]
  change (SupportedParameterDoubleUnit.doubleUnit f (op X.unop.obj) ≫
    (stableHomotopyFunctor 2).map (prespectrumMap ((ParameterModels.supported f).map
      (baseProductSwapMap (PolynomialLaurent.laurentProjection
        (.of (ULift ℤ))) (PolynomialLaurent.laurentProjection
          (.of (ULift ℤ))) X.unop.obj).op))) ≫ _ = _
  rw [SupportedParameterDoubleUnit.doubleUnit_swap, Preadditive.neg_comp]
  rfl

private theorem representative_transport {C : Type*} [Category C] {A B D E F G : C}
    (i : A ⟶ B) (b : B ⟶ D) (t : D ⟶ E) (v : A ⟶ F)
    (j : F ⟶ G) (q : G ⟶ D) (r : F ⟶ E)
    (hb : i ≫ b = v ≫ j ≫ q) (ht : j ≫ q ≫ t = r) :
    i ≫ b ≫ t = v ≫ r := by
  calc
    _ = (i ≫ b) ≫ t := (Category.assoc _ _ _).symm
    _ = (v ≫ j ≫ q) ≫ t := congrArg (fun k => k ≫ t) hb
    _ = v ≫ (j ≫ q ≫ t) := by simp only [Category.assoc]
    _ = _ := congrArg (fun k => v ≫ k) ht

variable {P' Q' : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (g : P' ⟶ Q')
  [IsOpenImmersion g.left]

/-- The original α₀ and α₁ represent the parameter comparison through both quotients. -/
theorem doubleForwardQuotient_coefficient (a : Under R) :
    (coefficientGroupIso g 0).hom.app a ≫
      (boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient g 0).app a ≫
      (coefficientDoubleQuotientIso g 2).hom.app a =
    (doubleForwardQuotient g.left).app (specRow.obj a) := by
  refine representative_transport
    ((coefficientGroupIso g 0).hom.app a)
    ((boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient g 0).app a)
    ((coefficientDoubleQuotientIso g 2).hom.app a)
    (SupportedParameterDoubleUnit.doubleUnit g.left (specUnder.obj a))
    ((prespectrumFunctor ⋙ stableHomotopyFunctor 2).map (doubleLaurentModelMap g a))
    (doubleContractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientSupportedPrespectrumFunctor g ⋙ stableHomotopyFunctor 2) a)
    (doubleContractionπ p m (quasiCompactStableFunctor g.left 2) (specRow.obj a)) ?_ ?_
  · exact doubleForwardQuotient_parameter g a
  · exact doubleLaurent_quotient g a 2

/-- Each genuine integral Spec fiber is invertible under the original supported QCQS hypotheses. -/
instance doubleForwardQuotient_spec_isIso [CompactSpace P'.left] [CompactSpace Q'.left]
    [QuasiSeparatedSpace Q'.left] (a : Under R) :
    IsIso ((doubleForwardQuotient g.left).app (specRow.obj a)) := by
  rw [← doubleForwardQuotient_coefficient g a]
  have := boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient_app_isIso g a 0
  infer_instance

/-- The actual degree-two quotient swap is minus identity at each integral Spec fiber. -/
theorem doubleContractionSwap_stableTwo_spec [CompactSpace P'.left] [CompactSpace Q'.left]
    [QuasiSeparatedSpace Q'.left] (a : Under R) :
    PolynomialLaurent.Relative.doubleContractionSwap
        (quasiCompactStableFunctor g.left 2) (specRow.obj a) = -𝟙 _ := by
  apply (cancel_epi ((doubleForwardQuotient g.left).app (specRow.obj a))).1
  rw [doubleForwardQuotient_swap, Preadditive.comp_neg, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules.SupportedParameterCoefficientUnitOperation

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.Bass.ModelDoubleLaurentSign
public import Colib.KTheory.Bass.TwoChartMapEpi

/-!
# The original connective cone as a quotient in degree zero

The actual cone inclusion descends through its original two chart relations.
The resulting map from the original Bass contraction of H-zero to the H-zero
of the actual unlooped cone is natural and epimorphic. It retains the original
inclusion as its representative; no quotient comparison is assumed invertible.

Adapted from the original construction in
`Quillen/KTheory/Bass/ModelConeZeroQuotient.lean`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open Topology Topology.LoopPrespectrum KTheory.Bass.TwoChart
universe u w
namespace KTheory.Bass.GeometricConeInterchange
local notation "p" => NatTrans.op PolynomialLaurent.Relative.plus
local notation "m" => NatTrans.op PolynomialLaurent.Relative.minus

/-- The unchanged single cone inclusion descended through the original two polynomial charts. -/
def coneZeroQuotientMap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (contraction p m (quasiCompactStableZero F)).obj X ⟶
      (quasiCompactStableZero (coneFunctor.obj F)).obj X :=
  contractionDescOfCharts p m (quasiCompactStableZero F) X
    ((stableHomotopyFunctor 0).map (coneInclusion F (op X.unop.obj)))
    (coneInclusion_zero_plus F hF (op X.unop.obj))
    (coneInclusion_zero_minus F hF (op X.unop.obj))

/-- The original quotient projection recovers the literal single cone inclusion. -/
@[reassoc]
theorem coneZeroQuotientMap_π (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (contractionπ p m (quasiCompactStableZero F)).app X ≫ coneZeroQuotientMap F hF X =
      (stableHomotopyFunctor 0).map (coneInclusion F (op X.unop.obj)) :=
  contractionπ_descOfCharts _ _ _ _ _ _ _

/-- Descending the actual epimorphic inclusion preserves its surjectivity. -/
theorem coneZeroQuotientMap_epi (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    Epi (coneZeroQuotientMap F hF X) :=
  @epi_of_epi_fac _ _ _ _ _ _ _ _ (coneInclusion_zero_epi F hF (op X.unop.obj))
    (coneZeroQuotientMap_π F hF X)

/-- Actual scheme naturality of the inclusion descends through the unchanged quotient. -/
@[reassoc]
theorem coneZeroQuotientMap_naturality (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X))
    {X Y : QuasiCompactSchemes.{u}ᵒᵖ} (f : X ⟶ Y) :
    (contraction p m (quasiCompactStableZero F)).map f ≫ coneZeroQuotientMap F hF Y =
      coneZeroQuotientMap F hF X ≫ (quasiCompactStableZero (coneFunctor.obj F)).map f := by
  apply contraction_hom_ext p m (quasiCompactStableZero F) X
  rw [← Category.assoc, ← (contractionπ p m (quasiCompactStableZero F)).naturality f,
    Category.assoc, coneZeroQuotientMap_π, ← Category.assoc, coneZeroQuotientMap_π]
  exact coneInclusion_zero_naturality F f.unop.hom.op

/-- The literal connective quotient comparison as a natural transformation on actual qc schemes. -/
def coneZeroQuotient (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) :
    contraction p m (quasiCompactStableZero F) ⟶ quasiCompactStableZero (coneFunctor.obj F) where
  app := coneZeroQuotientMap F hF
  naturality _ _ f := coneZeroQuotientMap_naturality F hF f

/-- Every component of the original connective quotient comparison is epimorphic. -/
instance coneZeroQuotient_app_epi (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    Epi ((coneZeroQuotient F hF).app X) := coneZeroQuotientMap_epi F hF X

end KTheory.Bass.GeometricConeInterchange

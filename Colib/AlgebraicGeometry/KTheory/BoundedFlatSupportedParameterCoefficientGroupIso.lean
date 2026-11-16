/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedParameterSpecQuotientTransport
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedParameterCoefficientUnitOperation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationEquivalence

/-!
# The actual supported stable row isomorphism at integral Spec parameters

The original supported parameter-to-coefficient row map is invertible on every
stable group, using its actual supported categorical restriction equivalence.
The induced double-quotient transport retains this map and the two specified
Laurent Spec legs. No quasi-compactness or separation assumption is needed for
this row comparison itself.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
SupportedParameterCoefficientGroupIso.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
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

/-- The unchanged supported stable group row on actual quasi-compact parameters. -/
def quasiCompactStableFunctor {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (d : ℤ) :
    QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  quasiCompactSchemesInclusion.op ⋙
    ((ParameterModels.supported f ⋙ prespectrumFunctor) ⋙ stableHomotopyFunctor d)

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The original supported row map induces an isomorphism on every actual stable group. -/
instance coefficientModelMap_stable_isIso (a : Under R) (d : ℤ) :
    IsIso ((prespectrumFunctor ⋙ stableHomotopyFunctor d).map (coefficientModelMap f a)) := by
  have hr := supportedRowRestriction_iterate_isStableEquivalence f
    (laurentUnderSquareFunctor R) 0 a d
  change IsIso ((prespectrumFunctor ⋙ stableHomotopyFunctor d).map
    ((supportedRowRestriction f).app a)) at hr
  change IsIso ((prespectrumFunctor ⋙ stableHomotopyFunctor d).map
    ((parameterSupportedRowIso f).hom.app a ≫ (supportedRowRestriction f).app a))
  rw [Functor.map_comp]
  infer_instance

/-- The specified supported row comparison, on the genuine integral Spec domain. -/
def coefficientGroupIso (d : ℤ) :
    specRow ⋙ quasiCompactStableFunctor f.left d ≅
      boundedAboveFlatCoefficientSupportedPrespectrumFunctor f ⋙ stableHomotopyFunctor d :=
  NatIso.ofComponents
    (fun a => asIso ((prespectrumFunctor ⋙ stableHomotopyFunctor d).map
      (coefficientModelMap f a))) (by
      intro a b g
      exact (Functor.whiskerRight
        ((parameterSupportedRowIso f).hom ≫ supportedRowRestriction f)
        (prespectrumFunctor ⋙ stableHomotopyFunctor d)).naturality g)

/-- The forward group comparison is exactly the original supported Model map. -/
@[simp]
theorem coefficientGroupIso_hom_app (d : ℤ) (a : Under R) :
    (coefficientGroupIso f d).hom.app a =
      (prespectrumFunctor ⋙ stableHomotopyFunctor d).map (coefficientModelMap f a) := rfl

/-- The two coefficient quotients map to the two actual qc parameter quotients at Spec. -/
def coefficientDoubleQuotientIso (d : ℤ) :
    contraction (underToLaurent R) (underToLaurentInvert R)
        (contraction (underToLaurent R) (underToLaurentInvert R)
          (boundedAboveFlatCoefficientSupportedPrespectrumFunctor f ⋙
            stableHomotopyFunctor d)) ≅
      specRow ⋙ contraction p m (contraction p m (quasiCompactStableFunctor f.left d)) :=
  (contractionFunctor (underToLaurent R) (underToLaurentInvert R)).mapIso
      ((contractionFunctor (underToLaurent R) (underToLaurentInvert R)).mapIso
        (coefficientGroupIso f d).symm) ≪≫
    doubleContractionIso (quasiCompactStableFunctor f.left d)

/-- The genuine quotient transport retains the original supported group comparison and
both actual Laurent Spec homomorphisms. -/
@[reassoc]
theorem coefficientDoubleQuotientIso_π (d : ℤ) (a : Under R) :
    doubleContractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedAboveFlatCoefficientSupportedPrespectrumFunctor f ⋙ stableHomotopyFunctor d) a ≫
      (coefficientDoubleQuotientIso f d).hom.app a =
    (coefficientGroupIso f d).inv.app
        ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)) ≫
      (quasiCompactStableFunctor f.left d).map
        (SupportedParameterSpecQuotientTransport.laurentIso.hom.app
            ((laurentUnderFunctor R).obj a) ≫
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.op.map
            (SupportedParameterSpecQuotientTransport.laurentIso.hom.app a)) ≫
      doubleContractionπ p m (quasiCompactStableFunctor f.left d) (specRow.obj a) := by
  simp only [coefficientDoubleQuotientIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, NatTrans.comp_app, contractionFunctor]
  rw [← Category.assoc, doubleContractionπ_groupMap, Category.assoc, doubleContractionIso_π]

end AlgebraicGeometry.Scheme.Modules.SupportedParameterCoefficientUnitOperation

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedParameterCoefficientDoubleOperation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedParameterCoefficientGroupIso

/-!
# Both original supported unit operations through the actual Spec quotients

The twice-Laurent endpoint comparison factors through the two original Laurent
Spec isomorphisms. The specified supported stable row isomorphism and both
original Laurent maps cancel against the actual double-cokernel transport.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
SupportedParameterSpecDoubleUnitTransport.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
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
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- Both retained Laurent endpoint maps factor through the actual qc Spec isomorphism. -/
theorem doubleLaurentModelMap_factor (a : Under R) :
    doubleLaurentModelMap f a =
      (ParameterModels.supported f.left).map
          (quasiCompactSchemesInclusion.op.map (doubleLaurentIso a).inv) ≫
        coefficientModelMap f ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)) := by
  change (ParameterModels.supported f.left).map
      (laurent.op.map (laurentSpecIso a.right).hom.op) ≫
      coefficientLaurentModelMap f ((laurentUnderFunctor R).obj a) =
    (ParameterModels.supported f.left).map
      (laurent.op.map (laurentSpecIso a.right).hom.op ≫
        (laurentSpecIso ((laurentUnderFunctor R).obj a).right).hom.op) ≫ _
  rw [coefficientLaurentModelMap_factor, Functor.map_comp, Category.assoc]

/-- The same exact factorization on stable groups retains the original supported row map. -/
theorem doubleLaurent_group_factor (a : Under R) (d : ℤ) :
    (prespectrumFunctor ⋙ stableHomotopyFunctor d).map (doubleLaurentModelMap f a) =
      (quasiCompactStableFunctor f.left d).map (doubleLaurentIso a).inv ≫
        (coefficientGroupIso f d).hom.app
          ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)) :=
  (congrArg (prespectrumFunctor ⋙ stableHomotopyFunctor d).map
    (doubleLaurentModelMap_factor f a)).trans
      ((prespectrumFunctor ⋙ stableHomotopyFunctor d).map_comp _ _)

private theorem quotient_transport_cancel {C : Type*} [Category C] {A B D E F : C}
    (e : D ≅ B) (l : D ≅ A) (v : A ⟶ B) (q : B ⟶ E) (t : E ⟶ F) (r : A ⟶ F)
    (hv : v = l.inv ≫ e.hom) (hq : q ≫ t = e.inv ≫ l.hom ≫ r) :
    v ≫ q ≫ t = r := by
  rw [hv, Category.assoc, hq]
  simp only [Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]

/-- The exact twice-Laurent comparison cancels against the two actual quotient transports. -/
theorem doubleLaurent_quotient (a : Under R) (d : ℤ) :
    (prespectrumFunctor ⋙ stableHomotopyFunctor d).map (doubleLaurentModelMap f a) ≫
      doubleContractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedAboveFlatCoefficientSupportedPrespectrumFunctor f ⋙ stableHomotopyFunctor d) a ≫
      (coefficientDoubleQuotientIso f d).hom.app a =
    doubleContractionπ p m (quasiCompactStableFunctor f.left d) (specRow.obj a) :=
  quotient_transport_cancel
    ((coefficientGroupIso f d).app
      ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)))
    ((quasiCompactStableFunctor f.left d).mapIso (doubleLaurentIso a)) _ _ _ _
    (doubleLaurent_group_factor f a d) (coefficientDoubleQuotientIso_π f d a)

end AlgebraicGeometry.Scheme.Modules.SupportedParameterCoefficientUnitOperation

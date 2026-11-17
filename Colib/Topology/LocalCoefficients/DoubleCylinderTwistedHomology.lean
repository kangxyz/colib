/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.LocalCoefficients.HomotopySquareChains
public import Colib.Topology.LocalCoefficients.SubspaceAcyclicQuasiIso
public import Colib.Topology.LocalCoefficients.UniverseLiftQuasiIso
public import Colib.Topology.DoubleMappingCylinder.CollarConnectivity
public import Colib.Topology.DoubleMappingCylinder.Gap

/-!
# Arbitrary local coefficients on the original double-cylinder legs

The local system on the actual pushout is arbitrary. Its literal restrictions
to the collars and overlap are retained throughout relative excision. Genuine
collar equivalences transfer the original attaching-map hypothesis using the
actual inverse-square homotopy and its coefficient transport. No constant
coefficient replacement, Pi-one calculation, cover, or desired leg certificate
is used.
-/
@[expose] public section

open TopCat.DoubleCylinder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval
universe u

namespace FundamentalGroupoid.LocalCoefficients
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
variable (lo hi : unitInterval) (b : Band lo hi)

include sq b

/-- The original left overlap inclusion preserves arbitrary target local systems
from the original attaching map's all-system quasi-isomorphisms. -/
theorem leftOverlap_twistedChainMap_quasiIso
    (hf : ∀ V : System.{u, u} B, QuasiIso (pushforwardChainMap f.hom V))
    (V : System.{u, u} (LeftCollar f g sq hi)) :
    QuasiIso (pushforwardChainMap (leftOverlapInclusion f g sq lo hi) V) := by
  have hhi : 0 < hi := lt_of_le_of_lt (bot_le : 0 ≤ lo) (b.property.1.trans b.property.2)
  exact pushforwardChainMap_quasiIso_of_equivalence_square
    (leftOverlapProjectionEquiv f g sq lo hi b)
    (leftCollarStrongDeformationRetract f g sq hi hhi).toHomotopyEquiv.symm
    f.hom (leftOverlapInclusion f g sq lo hi)
    (leftOverlap_projection_square f g sq lo hi b hhi) hf V

/-- The original right overlap inclusion preserves arbitrary target local systems
from the original attaching map's all-system quasi-isomorphisms. -/
theorem rightOverlap_twistedChainMap_quasiIso
    (hf : ∀ V : System.{u, u} C, QuasiIso (pushforwardChainMap g.hom V))
    (V : System.{u, u} (RightCollar f g sq lo)) :
    QuasiIso (pushforwardChainMap (rightOverlapInclusion f g sq lo hi) V) := by
  have hlo : lo < 1 := (b.property.1.trans b.property.2).trans_le (le_top : hi ≤ 1)
  exact pushforwardChainMap_quasiIso_of_equivalence_square
    (rightOverlapProjectionEquiv f g sq lo hi b)
    (rightCollarStrongDeformationRetract f g sq lo hlo).toHomotopyEquiv.symm
    g.hom (rightOverlapInclusion f g sq lo hi)
    (rightOverlap_projection_square f g sq lo hi b hlo) hf V

/-- Excision for the actual system on the pushout makes the pair relative to
its right collar acyclic, retaining every original coefficient restriction. -/
theorem doubleCylinder_rightCollar_twisted_relative_acyclic
    (hf : ∀ V : System.{u, u} B, QuasiIso (pushforwardChainMap f.hom V))
    (V : System.{u, u} D) :
    (relativeSingularChainComplex (rightCollarSet f g sq lo) V).Acyclic := by
  let U := leftCollarSet f g sq hi
  let W := rightCollarSet f g sq lo
  let VU := pullback (subspaceInclusion U) V
  have hq : QuasiIso (pushforwardChainMap
      (subspaceInclusion (intersectionInSubspace U W)) VU) :=
    leftOverlap_twistedChainMap_quasiIso f g sq lo hi b hf VU
  let S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
    ShortComplex.mk (pushforwardChainMap (subspaceInclusion (intersectionInSubspace U W))
      VU) (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have ha : (relativeSingularChainComplex (intersectionInSubspace U W) VU).Acyclic :=
    hS.acyclic_X₃ hq
  let q := relativePushforwardChainMap (subspaceInclusion U)
    (intersectionInSubspace U W) W (fun _ hx ↦ hx) V
  have hcover : U ∪ W = Set.univ := by
    exact collar_cover f g sq hi lo (b.property.1.trans b.property.2)
  have hq' : QuasiIso q := relativePushforwardChainMap_openExcision U W V
    (leftCollar_isOpen f g sq hi) (rightCollar_isOpen f g sq lo) hcover
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (ha n).isZero_homology.of_iso (isoOfQuasiIsoAt q n).symm

/-- Excision for the actual system on the pushout makes the pair relative to
its left collar acyclic, retaining every original coefficient restriction. -/
theorem doubleCylinder_leftCollar_twisted_relative_acyclic
    (hf : ∀ V : System.{u, u} C, QuasiIso (pushforwardChainMap g.hom V))
    (V : System.{u, u} D) :
    (relativeSingularChainComplex (leftCollarSet f g sq hi) V).Acyclic := by
  let U := rightCollarSet f g sq lo
  let W := leftCollarSet f g sq hi
  let VU := pullback (subspaceInclusion U) V
  have hq : QuasiIso (pushforwardChainMap
      (subspaceInclusion (intersectionInSubspace U W)) VU) :=
    rightOverlap_twistedChainMap_quasiIso f g sq lo hi b hf VU
  let S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
    ShortComplex.mk (pushforwardChainMap (subspaceInclusion (intersectionInSubspace U W))
      VU) (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have ha : (relativeSingularChainComplex (intersectionInSubspace U W) VU).Acyclic :=
    hS.acyclic_X₃ hq
  let q := relativePushforwardChainMap (subspaceInclusion U)
    (intersectionInSubspace U W) W (fun _ hx ↦ hx) V
  have hcover : U ∪ W = Set.univ := by
    simpa only [Set.union_comm] using
      collar_cover f g sq hi lo (b.property.1.trans b.property.2)
  have hq' : QuasiIso q := relativePushforwardChainMap_openExcision U W V
    (rightCollar_isOpen f g sq lo) (leftCollar_isOpen f g sq hi) hcover
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (ha n).isZero_homology.of_iso (isoOfQuasiIsoAt q n).symm

/-- The unchanged right end map is a quasi-isomorphism for every actual
pushout local system, from the opposite original attaching map's hypothesis. -/
theorem doubleCylinder_rightEnd_twistedChainMap_quasiIso
    (hf : ∀ V : System.{u, u} B, QuasiIso (pushforwardChainMap f.hom V))
    (V : System.{u, u} D) :
    QuasiIso (pushforwardChainMap (gapRightEndpoint e) V) := by
  have hcut : lo < 1 := (b.property.1.trans b.property.2).trans_le (le_top : hi ≤ 1)
  let W := rightCollarSet f g sq lo
  let j := subspaceInclusion W
  let c := (rightCollarInclusion f g sq lo hcut).hom
  have hj : QuasiIso (pushforwardChainMap j V) :=
    pushforwardChainMap_quasiIso_of_relative_acyclic W V
      (doubleCylinder_rightCollar_twisted_relative_acyclic f g sq lo hi b hf V)
  have hc : QuasiIso (pushforwardChainMap c (pullback j V)) :=
    pushforwardChainMap_quasiIso_of_homotopyEquiv
      (rightCollarStrongDeformationRetract f g sq lo hcut).toHomotopyEquiv (pullback j V)
  have ht : IsIso (coefficientChainMap (pullbackCompositionIso c j V).hom) := by
    change IsIso (coefficientChainIso (pullbackCompositionIso c j V)).hom
    infer_instance
  change QuasiIso (pushforwardChainMap (j.comp c) V)
  rw [pushforwardChainMap_comp]
  infer_instance

/-- The actual right end conclusion uses the original UniverseLift API, with
one common space/coefficient universe and no universe-resizing step. -/
theorem doubleCylinder_rightEnd_universeLift_quasiIso
    (hf : ∀ V : System.{u, u} B, QuasiIso (UniverseLift.chainMap.{u, u, u} f.hom V))
    (V : System.{u, u} D) :
    QuasiIso (UniverseLift.chainMap.{u, u, u} (gapRightEndpoint e) V) :=
  (UniverseLift.quasiIso_chainMap_iff _ V).mpr
    (doubleCylinder_rightEnd_twistedChainMap_quasiIso f g sq lo hi b
      (fun L ↦ (UniverseLift.quasiIso_chainMap_iff f.hom L).mp (hf L)) V)

/-- The unchanged left end map is a quasi-isomorphism for every actual
pushout local system, from the opposite original attaching map's hypothesis. -/
theorem doubleCylinder_leftEnd_twistedChainMap_quasiIso
    (hf : ∀ V : System.{u, u} C, QuasiIso (pushforwardChainMap g.hom V))
    (V : System.{u, u} D) :
    QuasiIso (pushforwardChainMap (gapLeftEndpoint e) V) := by
  have hcut : 0 < hi := lt_of_le_of_lt (bot_le : 0 ≤ lo) (b.property.1.trans b.property.2)
  let W := leftCollarSet f g sq hi
  let j := subspaceInclusion W
  let c := (leftCollarInclusion f g sq hi hcut).hom
  have hj : QuasiIso (pushforwardChainMap j V) :=
    pushforwardChainMap_quasiIso_of_relative_acyclic W V
      (doubleCylinder_leftCollar_twisted_relative_acyclic f g sq lo hi b hf V)
  have hc : QuasiIso (pushforwardChainMap c (pullback j V)) :=
    pushforwardChainMap_quasiIso_of_homotopyEquiv
      (leftCollarStrongDeformationRetract f g sq hi hcut).toHomotopyEquiv (pullback j V)
  have ht : IsIso (coefficientChainMap (pullbackCompositionIso c j V).hom) := by
    change IsIso (coefficientChainIso (pullbackCompositionIso c j V)).hom
    infer_instance
  change QuasiIso (pushforwardChainMap (j.comp c) V)
  rw [pushforwardChainMap_comp]
  infer_instance

/-- The actual left end conclusion uses the original UniverseLift API, with
one common space/coefficient universe and no universe-resizing step. -/
theorem doubleCylinder_leftEnd_universeLift_quasiIso
    (hf : ∀ V : System.{u, u} C, QuasiIso (UniverseLift.chainMap.{u, u, u} g.hom V))
    (V : System.{u, u} D) :
    QuasiIso (UniverseLift.chainMap.{u, u, u} (gapLeftEndpoint e) V) :=
  (UniverseLift.quasiIso_chainMap_iff _ V).mpr
    (doubleCylinder_leftEnd_twistedChainMap_quasiIso f g sq lo hi b
      (fun L ↦ (UniverseLift.quasiIso_chainMap_iff g.hom L).mp (hf L)) V)

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/DoubleCylinderTwistedHomology.lean:47-56"
  "adaptation" "Original cylinder legs and actual local systems"]
  leftOverlap_twistedChainMap_quasiIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/DoubleCylinderTwistedHomology.lean:60-69"
  "adaptation" "Original cylinder legs and actual local systems"]
  rightOverlap_twistedChainMap_quasiIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/DoubleCylinderTwistedHomology.lean:73-97"
  "adaptation" "Original cylinder legs and actual local systems"]
  doubleCylinder_rightCollar_twisted_relative_acyclic

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/DoubleCylinderTwistedHomology.lean:101-126"
  "adaptation" "Original cylinder legs and actual local systems"]
  doubleCylinder_leftCollar_twisted_relative_acyclic

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/DoubleCylinderTwistedHomology.lean:130-149"
  "adaptation" "Original cylinder legs and actual local systems"]
  doubleCylinder_rightEnd_twistedChainMap_quasiIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/DoubleCylinderTwistedHomology.lean:153-159"
  "adaptation" "Original cylinder legs and actual local systems"]
  doubleCylinder_rightEnd_universeLift_quasiIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/DoubleCylinderTwistedHomology.lean:163-182"
  "adaptation" "Original cylinder legs and actual local systems"]
  doubleCylinder_leftEnd_twistedChainMap_quasiIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/DoubleCylinderTwistedHomology.lean:186-192"
  "adaptation" "Original cylinder legs and actual local systems"]
  doubleCylinder_leftEnd_universeLift_quasiIso

end FundamentalGroupoid.LocalCoefficients

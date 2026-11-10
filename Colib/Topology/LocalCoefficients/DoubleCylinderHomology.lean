/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.LocalCoefficients.ConstantChainMaps
public import Colib.Topology.LocalCoefficients.OpenExcision
public import Colib.Topology.DoubleMappingCylinder.CollarConnectivity

/-! # Actual double-cylinder homology from the original attaching-map quasi-isomorphism -/
@[expose] public section

open TopCat.DoubleCylinder

noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval
universe u
namespace FundamentalGroupoid.LocalCoefficients
open TopCat.DoubleCylinder
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (lo hi : unitInterval) (b : Band lo hi) (V : ModuleCat.{u} ℤ)

include sq b

/-- The actual overlap inclusion is a constant-chain quasi-isomorphism when the original f is. -/
theorem leftOverlap_constantChainMap_quasiIso
    (hf : QuasiIso (pushforwardChainMap f.hom (constant B V))) :
    QuasiIso (pushforwardChainMap (leftOverlapInclusion f g sq lo hi)
      (constant (LeftCollar f g sq hi) V)) := by
  let := hf
  have hhi : 0 < hi := lt_of_le_of_lt (bot_le : 0 ≤ lo) (b.property.1.trans b.property.2)
  let p := (leftCollarProjection f g sq hi hhi).hom
  let s := (leftOverlapProjectionEquiv f g sq lo hi b).toFun
  let i := leftOverlapInclusion f g sq lo hi
  have hp : QuasiIso (pushforwardChainMap p (constant B V)) :=
    pushforwardChainMap_quasiIso_of_homotopyEquiv
      (leftCollarStrongDeformationRetract f g sq hi hhi).toHomotopyEquiv.symm (constant B V)
  have hs : QuasiIso (pushforwardChainMap s (constant A V)) :=
    pushforwardChainMap_quasiIso_of_homotopyEquiv
      (leftOverlapProjectionEquiv f g sq lo hi b) (constant A V)
  let := hp
  let := hs
  have hcomp : QuasiIso (pushforwardChainMap (p.comp i) (constant B V)) := by
    rw [leftOverlap_projection_square f g sq lo hi b hhi,
      constant_pushforwardChainMap_comp]
    exact quasiIso_comp (pushforwardChainMap s (constant A V))
      (pushforwardChainMap f.hom (constant B V)) (hφ := hs) (hφ' := hf)
  rw [constant_pushforwardChainMap_comp] at hcomp
  exact (quasiIso_iff_comp_right _ _ (hφ' := hp)).mp hcomp

/-- Excision makes the genuine double-cylinder pair relative to its right collar acyclic. -/
theorem doubleCylinder_rightCollar_relative_acyclic
    (hf : QuasiIso (pushforwardChainMap f.hom (constant B V))) :
    (relativeSingularChainComplex (rightCollarSet f g sq lo) (constant D V)).Acyclic := by
  let U := leftCollarSet f g sq hi
  let W := rightCollarSet f g sq lo
  have hq : QuasiIso (pushforwardChainMap
      (subspaceInclusion (intersectionInSubspace U W)) (constant U V)) :=
    leftOverlap_constantChainMap_quasiIso f g sq lo hi b V hf
  let S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
    ShortComplex.mk (pushforwardChainMap (subspaceInclusion (intersectionInSubspace U W))
      (constant U V)) (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have ha : (relativeSingularChainComplex (intersectionInSubspace U W)
      (constant U V)).Acyclic := hS.acyclic_X₃ hq
  let q := relativePushforwardChainMap (subspaceInclusion U)
    (intersectionInSubspace U W) W (fun _ hx ↦ hx) (constant D V)
  have hq' : QuasiIso q :=
    relativePushforwardChainMap_openExcision U W (constant D V)
      (leftCollar_isOpen f g sq hi) (rightCollar_isOpen f g sq lo)
      (collar_cover f g sq hi lo (b.property.1.trans b.property.2))
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (ha n).isZero_homology.of_iso (isoOfQuasiIsoAt q n).symm

/-- If the right end has zero homology in a specified degree, the actual double cylinder does
too. -/
theorem doubleCylinder_homology_isZero_of_quasiIso
    (hf : QuasiIso (pushforwardChainMap f.hom (constant B V))) (n : ℕ)
    (hC : IsZero (homology (constant C V) n)) :
    IsZero (homology (constant D V) n) := by
  have hlo : lo < 1 := (b.property.1.trans b.property.2).trans_le (le_top : hi ≤ 1)
  let p := (rightCollarProjection f g sq lo hlo).hom
  have hp : IsIso (pushforwardHomologyMap p (constant C V) n) :=
    isIso_pushforwardHomologyMap_of_homotopyEquiv
      (rightCollarStrongDeformationRetract f g sq lo hlo).toHomotopyEquiv.symm
      (constant C V) n
  let := hp
  have hW : IsZero (homology (constant (RightCollar f g sq lo) V) n) :=
    hC.of_iso (@asIso _ _ _ _ (pushforwardHomologyMap p (constant C V) n) hp)
  let S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
    ShortComplex.mk (pushforwardChainMap (subspaceInclusion (rightCollarSet f g sq lo))
      (constant D V)) (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hrel := (doubleCylinder_rightCollar_relative_acyclic f g sq lo hi b V hf n).isZero_homology
  exact (hS.homology_exact₂ n).isZero_X₂ (hW.eq_of_src _ _) (hrel.eq_of_tgt _ _)

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/DoubleCylinderHomology.lean:34-53"
  "adaptation" "Original attaching map and actual collar-relative chain complexes"]
  leftOverlap_constantChainMap_quasiIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/DoubleCylinderHomology.lean:56-78"
  "adaptation" "Original attaching map and actual collar-relative chain complexes"]
  doubleCylinder_rightCollar_relative_acyclic

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/DoubleCylinderHomology.lean:82-99"
  "adaptation" "Original attaching map and actual collar-relative chain complexes"]
  doubleCylinder_homology_isZero_of_quasiIso

attribute [colib_tag "COL-0524"]
  doubleCylinder_rightCollar_relative_acyclic
  doubleCylinder_homology_isZero_of_quasiIso

end FundamentalGroupoid.LocalCoefficients

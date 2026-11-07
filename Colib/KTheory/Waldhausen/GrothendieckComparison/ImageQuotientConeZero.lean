/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.ImageQuotientCone
public import Colib.KTheory.Waldhausen.GrothendieckComparison.ImageQuotientExact
public import Colib.KTheory.Waldhausen.Iterated.ConeStableSequence
public import Colib.KTheory.Waldhausen.Iterated.StableFunctoriality
public import Colib.Topology.Prespectrum.ConeDescZeroComparison

/-!
# The unchanged image-quotient cone map on stable degree zero

The actual original K-map kernel and surjectivity transfer through the original stable
comparison. They identify the previously constructed cone descent, retaining its specified
nullhomotopy and both original categorical maps.
-/

/-! Implementation provenance:
`Quillen/Waldhausen/GrothendieckComparison/ImageQuotientConeZero.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, endpoint casts, complete homotopies and hypotheses are retained
under their native mathematical owners. -/
@[expose] public section

open CategoryTheory.Waldhausen.IteratedS

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u v
namespace CategoryTheory.Waldhausen.AlgebraicGrothendieck

open Topology
open IteratedS Topology.LoopPrespectrum
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) {V : Structure D} (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (T : FunctorialFactorization V.asSmall)

include T in
/-- Genuine original image exactness makes the actual unshifted cone map a degree-zero bijection. -/
theorem imageQuotientConeMap_stable_zero_bijective :
    Function.Bijective ((stableHomotopyFunctor 0).map (imageQuotientConeMap W F hF)) := by
  let d := imageQuotientGrading W F hF
  let f := exactOriginalPrespectrumMap W V hF
  let g := Fibration.changeWeakPrespectrumMap d.nested
  let N := imageQuotientPrespectrumNullhomotopy W F hF
  let q := Fibration.changeWeak_exact d.nested
  let eW := originalKStableEquiv W 0
  let eV := originalKStableEquiv V 0
  let eG := originalKStableEquiv d.coarseStructure 0
  have nq (a : V.K 0) : (stableHomotopyFunctor 0).map g (eV (Additive.ofMul a)) =
      eG (Additive.ofMul (KMap q 0 a)) :=
    (originalKStableEquiv_naturality V d.coarseStructure q d.nested.zero_eq.symm 0 a).symm
  have hf : IsStableEquivalence (mappingConeFiberComparison f) :=
    originalPrespectrum_mappingConeFiberComparison_isStableEquivalence W V f
  let : Subsingleton (stableHomotopyGroup (originalPrespectrum W) (-1)) :=
    originalStableHomotopyGroup_neg_subsingleton W (-1) (by omega)
  apply mappingConeDesc_stable_zero_bijective f g N hf
  · intro x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := eV.surjective x
      have hz : KMap q 0 a.toMul = 1 := by
        have h := eG.injective ((nq a.toMul).symm.trans (hx.trans (map_zero eG).symm))
        exact congrArg Additive.toMul h
      have ha : a.toMul ∈ (KMap hF 0).range := by
        rw [imageQuotient_changeWeakKMap_range_ker W F hF T]
        exact hz
      obtain ⟨b, hb⟩ := ha
      refine ⟨eW (Additive.ofMul b), ?_⟩
      exact (originalKStableEquiv_exact_naturality W V hF 0 b).symm.trans
        (congrArg (fun z ↦ eV (Additive.ofMul z)) hb)
    · rintro ⟨b, hb⟩
      have hc : (stableHomotopyFunctor 0).map f ≫ (stableHomotopyFunctor 0).map g = 0 := by
        exact ((stableHomotopyFunctor 0).map_comp f g).symm.trans
          ((N.stableHomotopyMap_eq 0).trans
            (stableHomotopyMap_zero (originalPrespectrum W)
              (originalPrespectrum d.coarseStructure) 0))
      exact (congrArg ((stableHomotopyFunctor 0).map g) hb).symm.trans
        (ConcreteCategory.congr_hom hc b)
  · intro y
    obtain ⟨a, rfl⟩ := eG.surjective y
    obtain ⟨b, hb⟩ := imageQuotient_changeWeakKMap_surjective W F hF T a.toMul
    exact ⟨eV (Additive.ofMul b), (nq b).trans
      (congrArg (fun z ↦ eG (Additive.ofMul z)) hb)⟩

end CategoryTheory.Waldhausen.AlgebraicGrothendieck

attribute [colib_tag "COL-0290",
  colib_ref "ThomasonTrobaugh1990" "Sections 1.5.6-1.5.7, p. 261" "ingredient"
    "K-zero relations and representatives underlie the actual degree-zero cone comparison"]
  CategoryTheory.Waldhausen.AlgebraicGrothendieck.imageQuotientConeMap_stable_zero_bijective

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.PairTorAction
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleRegularImmersion
public import Colib.RingTheory.Koszul.RestrictionComparison
public import Mathlib.RingTheory.Regular.Flat

/-!
# Original pair Tor and its original middle-list support Koszul module

A regular generating list in the original Y self-product stalk pulls back along the actual
flat middle-pair map. Native ideal base change identifies its span with the actual diagonal
stalk kernel. The native quotient Tor comparison and the free Koszul restriction comparison
then identify the original pair Tor with the full support-ring coefficient Koszul homology.

The comparison is linear over the actual support local ring: its action on Tor is the
restriction of the canonical full incidence action, and the commuting original stalk maps
prove compatibility with ambient scalars. Native extension of linearity along a surjection
supplies the support-linear equivalence. No module or comparison is assumed by the caller.

This is the original pair input to the full-exterior flat base-change comparison. Regularity
is required only for the list in the original middle stalk, not for its image in a support
ring. The support product and the incidence retain their full scheme structures.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The original support scalar map, including the actual equality of ambient image points. -/
def correspondenceIncidenceSupportStalkMap (x : correspondenceIncidence f g h z w) :
    correspondenceIncidenceAmbientStalk f g h z w x →+*
      (correspondenceSupportProduct f g h z w).presheaf.stalk
        (correspondenceIncidenceToSupportProduct f g h z w x) :=
  (((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceIncidence_ambient_point_eq f g h z w x))).hom ≫
      (correspondenceSupportProductInclusion f g h z w).stalkMap
        (correspondenceIncidenceToSupportProduct f g h z w x)).hom

/-- The original support scalar map is surjective, including the point transport. -/
theorem correspondenceIncidenceSupportStalkMap_surjective
    (x : correspondenceIncidence f g h z w) :
    Function.Surjective (correspondenceIncidenceSupportStalkMap f g h z w x) :=
  (SurjectiveOnStalks.stalkMap_surjective (correspondenceSupportProductInclusion f g h z w)
    (correspondenceIncidenceToSupportProduct f g h z w x)).comp
      (ConcreteCategory.bijective_of_isIso
        ((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
          (Inseparable.of_eq (correspondenceIncidence_ambient_point_eq f g h z w x))).hom).2

/-- The ambient-to-incidence stalk map factors through the actual support stalk map. -/
theorem correspondenceIncidenceSupportStalkMap_comp
    (x : correspondenceIncidence f g h z w) :
    (((correspondenceIncidenceToSupportProduct f g h z w).stalkMap x).hom).comp
        (correspondenceIncidenceSupportStalkMap f g h z w x) =
      ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom := by
  have he := Scheme.Hom.stalkMap_congr_hom
    (correspondenceIncidenceAmbientInclusion f g h z w)
    (correspondenceIncidenceToSupportProduct f g h z w ≫
      correspondenceSupportProductInclusion f g h z w)
    (correspondenceIncidence_ambient_comm f g h z w) x
  change ((((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceIncidence_ambient_point_eq f g h z w x))).hom ≫
      (correspondenceSupportProductInclusion f g h z w).stalkMap
        (correspondenceIncidenceToSupportProduct f g h z w x)) ≫
      (correspondenceIncidenceToSupportProduct f g h z w).stalkMap x).hom = _
  rw [Category.assoc, ← Scheme.Hom.stalkMap_comp]
  exact congrArg (fun a => a.hom) he.symm

/-- Support scalars act on original pair Tor through its canonical full-incidence action. -/
@[instance_reducible]
def correspondenceIncidenceTorSupportModule [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    Module ((correspondenceSupportProduct f g h z w).presheaf.stalk
      (correspondenceIncidenceToSupportProduct f g h z w x))
        (correspondenceIncidenceAmbientTor f g h z w x n) := by
  letI := correspondenceIncidenceTorModule f g h z w x n
  exact Module.compHom _ ((correspondenceIncidenceToSupportProduct f g h z w).stalkMap x).hom

/-- The actual support action restricts to the original ambient Tor action. -/
theorem correspondenceIncidenceTorSupportScalarTower [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    let := (correspondenceIncidenceSupportStalkMap f g h z w x).toAlgebra
    let := correspondenceIncidenceTorSupportModule f g h z w x n
    IsScalarTower (correspondenceIncidenceAmbientStalk f g h z w x)
      ((correspondenceSupportProduct f g h z w).presheaf.stalk
        (correspondenceIncidenceToSupportProduct f g h z w x))
      (correspondenceIncidenceAmbientTor f g h z w x n) := by
  let := (correspondenceIncidenceSupportStalkMap f g h z w x).toAlgebra
  let := correspondenceIncidenceTorModule f g h z w x n
  let := correspondenceIncidenceTorSupportModule f g h z w x n
  refine ⟨fun a d m => ?_⟩
  change ((correspondenceIncidenceToSupportProduct f g h z w).stalkMap x).hom
      (correspondenceIncidenceSupportStalkMap f g h z w x a * d) • m =
    a • (((correspondenceIncidenceToSupportProduct f g h z w).stalkMap x).hom d • m)
  rw [map_mul, mul_smul]
  have he := congrArg (fun φ => φ a) (correspondenceIncidenceSupportStalkMap_comp f g h z w x)
  change ((correspondenceIncidenceToSupportProduct f g h z w).stalkMap x).hom
    (correspondenceIncidenceSupportStalkMap f g h z w x a) =
      ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom a at he
  rw [he, correspondenceIncidenceTorModule_stalkMap_smul]

/-- The original diagonal quotient is its actual triple-product stalk as an ambient module. -/
def correspondenceIncidenceDiagonalStalkQuotientIso [IsSeparated g]
    (x : correspondenceIncidence f g h z w) :
    ModuleCat.of (correspondenceIncidenceAmbientStalk f g h z w x)
      (correspondenceIncidenceAmbientStalk f g h z w x ⧸
        RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap
          (correspondenceIncidenceInclusion f g h z w x)).hom) ≅
      correspondenceIncidenceTripleStalkModule f g h z w x := by
  let A := correspondenceIncidenceAmbientStalk f g h z w x
  let B := (correspondenceTripleProduct f g h).presheaf.stalk
    (correspondenceIncidenceInclusion f g h z w x)
  let ψ : A →+* B := ((correspondenceTripleInclusion f g h).stalkMap
    (correspondenceIncidenceInclusion f g h z w x)).hom
  letI : Algebra A B := ψ.toAlgebra
  exact (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B)
    (SurjectiveOnStalks.stalkMap_surjective (correspondenceTripleInclusion f g h)
      (correspondenceIncidenceInclusion f g h z w x))).toLinearEquiv.toModuleIso

/-- The same original middle-stalk list is regular and generates the actual pair-diagonal kernel. -/
theorem correspondenceOriginalMiddleList_pair_regular [Flat f] [Flat h] [IsSeparated g]
    (q : correspondenceTripleProduct f g h) {r : ℕ}
    (t : Fin r → (pullback g g).presheaf.stalk
      (correspondenceMiddlePair f g h (correspondenceTripleInclusion f g h q)))
    (ht : IsRegular ((pullback g g).presheaf.stalk
      (correspondenceMiddlePair f g h (correspondenceTripleInclusion f g h q))) (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h (correspondenceTripleInclusion f g h q)) =
        Ideal.span (Set.range t)) :
    let p := correspondenceTripleInclusion f g h q
    let β := ((correspondenceMiddlePair f g h).stalkMap p).hom
    IsRegular ((correspondenceIntersectionAmbient f g h).presheaf.stalk p)
      (List.ofFn (fun j => β (t j))) ∧
    RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap q).hom =
      Ideal.span (Set.range (fun j => β (t j))) := by
  dsimp only
  let p := correspondenceTripleInclusion f g h q
  let A := (correspondenceIntersectionAmbient f g h).presheaf.stalk p
  let R := (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h p)
  let β : R →+* A := ((correspondenceMiddlePair f g h).stalkMap p).hom
  constructor
  · let : Algebra R A := β.toAlgebra
    have : Module.Flat R A := Flat.stalkMap (correspondenceMiddlePair f g h) p
    have : IsLocalHom (algebraMap R A) := by
      change IsLocalHom ((correspondenceMiddlePair f g h).stalkMap p).hom
      infer_instance
    have : Module.FaithfullyFlat R A := Module.FaithfullyFlat.of_flat_of_isLocalHom
    change IsRegular A (List.ofFn (fun j => β (t j)))
    have hr : IsRegular A ((List.ofFn t).map (algebraMap R A)) := ht.of_faithfullyFlat
    change IsRegular A ((List.ofFn t).map β) at hr
    simpa only [List.map_ofFn, Function.comp_def] using hr
  · have hp : pullback.diagonal g (correspondenceTripleMiddle f g h q) =
        correspondenceMiddlePair f g h p := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun m => m q) (correspondenceTriple_isPullback f g h).w
    have hk := Stacks.Flatness.ker_stalkMap_of_isPullback
      (correspondenceTriple_isPullback f g h).flip q hp
    have hc {u v : pullback (C := Scheme) g g} (e : u = v) :
        (IdealSheafData.stalk (pullback.diagonal g).ker u).map
          ((pullback g g).presheaf.stalkCongr (Inseparable.of_eq e)).hom.hom =
            IdealSheafData.stalk (pullback.diagonal g).ker v := by
      subst v
      simp [TopCat.Presheaf.stalkCongr]
    rw [ker_stalkMap_eq_idealStalk_ker (pullback.diagonal g)
      (correspondenceTripleMiddle f g h q), CommRingCat.hom_comp, ← Ideal.map_map, hc hp,
      hkt, Ideal.map_span, ← Set.range_comp] at hk
    exact hk

/-- Original pair Tor is the native support Koszul homology of the same original middle list. -/
def correspondenceIncidenceTorIsoOriginalSupportKoszul [Flat f] [Flat h] [IsSeparated g]
    (x : correspondenceIncidence f g h z w) {r : ℕ}
    (t : Fin r → (pullback g g).presheaf.stalk
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w x)))
    (ht : IsRegular ((pullback g g).presheaf.stalk
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w x)))
        (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w x)) =
        Ideal.span (Set.range t)) (n : ℕ) :
    let D := (correspondenceSupportProduct f g h z w).presheaf.stalk
      (correspondenceIncidenceToSupportProduct f g h z w x)
    let φ := correspondenceIncidenceSupportStalkMap f g h z w x
    let β := ((correspondenceMiddlePair f g h).stalkMap
      (correspondenceIncidenceAmbientInclusion f g h z w x)).hom
    correspondenceIncidenceAmbientTor f g h z w x n ≅
      (ModuleCat.restrictScalars φ).obj
        ((Koszul.seqComplexTensor (fun j => φ (β (t j))) D).homology n) := by
  let A := correspondenceIncidenceAmbientStalk f g h z w x
  let D := (correspondenceSupportProduct f g h z w).presheaf.stalk
    (correspondenceIncidenceToSupportProduct f g h z w x)
  let φ := correspondenceIncidenceSupportStalkMap f g h z w x
  let β := ((correspondenceMiddlePair f g h).stalkMap
    (correspondenceIncidenceAmbientInclusion f g h z w x)).hom
  let a : Fin r → A := fun j => β (t j)
  let M := correspondenceIncidenceSupportStalkModule f g h z w x
  let J := RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap
    (correspondenceIncidenceInclusion f g h z w x)).hom
  let Q := ModuleCat.of A (A ⧸ J)
  letI : Algebra A D := φ.toAlgebra
  obtain ⟨hr, hk⟩ := correspondenceOriginalMiddleList_pair_regular f g h
    (correspondenceIncidenceInclusion f g h z w x) t ht hkt
  exact ((Tor (ModuleCat A) n).obj M).mapIso
      (correspondenceIncidenceDiagonalStalkQuotientIso f g h z w x).symm ≪≫
    (((Tor_iso_Tor' A n) ≪≫ (torFlip_iso_Tor' A n).symm).app M).app Q ≪≫
    Koszul.torIsoHomologySeqComplexTensorOfIsRegular a hr J hk M n ≪≫
    Koszul.homologySeqComplexTensorRestrictScalarsIso a (ModuleCat.of D D) n

/-- The comparison is linear over the actual support ring with the quotient-induced Tor action. -/
def correspondenceIncidenceTorOriginalSupportLinearEquiv
    [Flat f] [Flat h] [IsSeparated g] (x : correspondenceIncidence f g h z w) {r : ℕ}
    (t : Fin r → (pullback g g).presheaf.stalk
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w x)))
    (ht : IsRegular ((pullback g g).presheaf.stalk
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w x)))
        (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w x)) =
        Ideal.span (Set.range t)) (n : ℕ) :
    let D := (correspondenceSupportProduct f g h z w).presheaf.stalk
      (correspondenceIncidenceToSupportProduct f g h z w x)
    let φ := correspondenceIncidenceSupportStalkMap f g h z w x
    let β := ((correspondenceMiddlePair f g h).stalkMap
      (correspondenceIncidenceAmbientInclusion f g h z w x)).hom
    letI := correspondenceIncidenceTorSupportModule f g h z w x n
    correspondenceIncidenceAmbientTor f g h z w x n ≃ₗ[D]
      ((Koszul.seqComplexTensor (fun j => φ (β (t j))) D).homology n) := by
  let A := correspondenceIncidenceAmbientStalk f g h z w x
  let D := (correspondenceSupportProduct f g h z w).presheaf.stalk
    (correspondenceIncidenceToSupportProduct f g h z w x)
  let φ := correspondenceIncidenceSupportStalkMap f g h z w x
  letI : Algebra A D := φ.toAlgebra
  letI := correspondenceIncidenceTorSupportModule f g h z w x n
  letI := correspondenceIncidenceTorSupportScalarTower f g h z w x n
  let β := ((correspondenceMiddlePair f g h).stalkMap
    (correspondenceIncidenceAmbientInclusion f g h z w x)).hom
  let N := (Koszul.seqComplexTensor (fun j => φ (β (t j))) D).homology n
  letI : Module A N := Module.compHom N φ
  letI : IsScalarTower A D N := IsScalarTower.of_compHom A D N
  let e : correspondenceIncidenceAmbientTor f g h z w x n ≃ₗ[A] N :=
    (correspondenceIncidenceTorIsoOriginalSupportKoszul f g h z w x t ht hkt n).toLinearEquiv
  exact e.extendScalarsOfSurjective
    (correspondenceIncidenceSupportStalkMap_surjective f g h z w x)

end Stacks.Chow

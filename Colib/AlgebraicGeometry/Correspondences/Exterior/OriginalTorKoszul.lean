/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.OriginalTorStalkMaps

/-!
# Original native Tor in the same actual remaining-Y ordered list

SOURCE_ONLY_UNCOMPILED. For the constructed remaining family F at an actual
exterior incidence point x, set s₀ = F.originalCoefficientList and
C₀ = P₀.stalk(q(c(x))). The native original ambient Tor at π(x), with its
existing full-incidence action restricted along the actual η₀, is C₀-linearly
equivalent to H_n(K(s₀.get; C₀)) in every degree n, including zero.

The only chosen list is F.baseList. Its stalkCongr image is used in the accepted
original support comparison. The full diagonal ideal and ambient regularity
come from the actual family and the original flat X/Z ambient maps; regularity
of s₀ and flatness of the supports over Y are neither required nor asserted.
The entrywise scalar square identifies the coefficient equations literally.

This is only the original-side K2 comparison. It does not assemble exterior
Tor, incidence base change, lengths, Euler coefficients, or composition cycles.
The constructed family uses choice, and no choice-independent naturality of
this equivalence is claimed. The public original Tor comparison is the existing
Colib e7697ab8164435c7093665d02ac34f021eefb75e,
Colib/AlgebraicGeometry/Correspondences/Composition/PairOriginalKoszulTor.lean:223-256.
The separate report distinguishes that input from the source-only geometry and
this new actual-point application.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  (x : nativeExteriorIncidence X Y Z T z w hz hw)

local notation3 (prettyPrint := false) "P₀" =>
  correspondenceSupportProduct X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "q" =>
  nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw
local notation3 (prettyPrint := false) "π" => nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "iQ" =>
  nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "r" => exteriorAmbientRemainingPair X Y Z T
local notation3 (prettyPrint := false) "C₀" => (P₀).presheaf.stalk (q (c x))
local notation3 (prettyPrint := false) "T₀" =>
  correspondenceIncidenceAmbientTor X.hom Y.hom Z.hom z w (π x)
local notation3 (prettyPrint := false) "F" =>
  nativeExteriorRemainingStalkFamily X Y T z hz Z w hw x
local notation3 (prettyPrint := false) "u₀" =>
  (nativeExteriorRemainingOriginalStalkMap X Y T z hz Z w hw x).hom

/-- The one chosen list is transported to the original ambient Y point, with its full ideal. -/
theorem nativeExteriorOriginalTor_middleList_regular :
    let e := nativeExteriorOriginalTorMiddleStalkIso X Y Z T z w hz hw x
    let t := fun j => e.hom.hom ((F).baseList.get j)
    let y := correspondenceMiddlePair X.hom Y.hom Z.hom
      (correspondenceIncidenceAmbientInclusion X.hom Y.hom Z.hom z w (π x))
    IsRegular ((pullback Y.hom Y.hom).presheaf.stalk y) (List.ofFn t) ∧
      IdealSheafData.stalk (pullback.diagonal Y.hom).ker y = Ideal.span (Set.range t) :=
  correspondenceOriginalMiddleList_stalkCongr X.hom Y.hom Z.hom z w (π x)
    (r (iQ (c x))) (nativeExteriorOriginalTor_middlePoint X Y Z T z w hz hw x)
    (F).baseList (F).base_regular (F).base_ideal

/-- The coefficient equations are the literal ordered image of F.baseList, including its length. -/
theorem nativeExteriorOriginalTor_coefficient_ofFn :
    List.ofFn (fun j => (u₀) ((F).baseList.get j)) = (F).originalCoefficientList := by
  rw [List.ofFn_comp', List.ofFn_get]

/-- Original native ambient Tor is C₀-linear Koszul homology of the same remaining list.
C₀ acts through the actual η₀ on the already existing native incidence Tor module. -/
def nativeExteriorOriginalTorRemainingKoszulEquiv (n : ℕ) :
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    T₀ n ≃ₗ[C₀]
      ((Koszul.seqComplexTensor (F).originalCoefficientList.get C₀).homology n) := by
  let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
  let e := correspondenceIncidenceTorSupportLinearEquivOfPoints
    X.hom Y.hom Z.hom z w (π x) (q (c x))
    (nativeExteriorIncidenceQuotient_point X Y Z T z w hz hw x).symm
    (r (iQ (c x))) (nativeExteriorOriginalTor_middlePoint X Y Z T z w hz hw x)
    (F).baseList (F).base_regular (F).base_ideal n
  have he : T₀ n ≃ₗ[C₀]
      ((Koszul.seqComplexTensor
        (fun j => nativeExteriorOriginalTorMiddleStalkMap X Y Z T z w hz hw x
          ((F).baseList.get j)) C₀).homology n) := e
  rw [nativeExteriorOriginalTorMiddleStalkMap_eq] at he
  have hc : Koszul.seqComplexTensor (F).originalCoefficientList.get C₀ =
      Koszul.seqComplexTensor (fun j => (u₀) ((F).baseList.get j)) C₀ := by
    change Koszul.seqComplexTensor ((F).baseList.map u₀).get C₀ = _
    have aux {r₁ r₂ : ℕ} (hlen : r₁ = r₂) (f₁ : Fin r₁ → C₀) (f₂ : Fin r₂ → C₀)
        (hfun : HEq f₁ f₂) :
        Koszul.seqComplexTensor f₁ C₀ = Koszul.seqComplexTensor f₂ C₀ := by
      subst r₂
      cases hfun
      rfl
    apply aux (List.length_map (as := (F).baseList) u₀)
    apply (Fin.heq_fun_iff (List.length_map (as := (F).baseList) u₀)).mpr
    intro idx
    simp only [List.get_eq_getElem, List.getElem_map]
  rw [hc]
  exact he

/-- The actual comparison is linear for C₀ acting through η₀ on native original Tor. -/
theorem nativeExteriorOriginalTorRemainingKoszulEquiv_map_smul
    (n : ℕ) (a : C₀) (t : T₀ n) :
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n (a • t) =
      a • nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n t := by
  let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
  exact (nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n).map_smul a t

/-- The inverse cancels on the actual original native Tor, including at degree zero. -/
theorem nativeExteriorOriginalTorRemainingKoszulEquiv_symm_apply_apply
    (n : ℕ) (t : T₀ n) :
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    (nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n).symm
      (nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n t) = t := by
  let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
  exact (nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n).symm_apply_apply t

end Stacks.Chow

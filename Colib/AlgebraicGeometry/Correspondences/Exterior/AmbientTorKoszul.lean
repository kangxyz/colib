/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.AmbientTorStalkMaps
public import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterStalkFamily
public import Colib.Algebra.Category.ModuleCat.Tor.RegularBlock
public import Mathlib.Data.List.OfFn

/-!
# Native exterior ambient Tor and the actual remaining coefficient Koszul homology

SOURCE_ONLY_UNCOMPILED. At every actual exterior incidence point, in every
natural degree, the native ambient Tor (in its native support, triple order)
is isomorphic over its native ambient stalk to the remaining coefficient Koszul
homology restricted along the actual ambient-to-coefficient map.

The leading and remaining families are constructed from the actual geometry.
No common list, quotient comparison, leading Tor vanishing, or conclusion-shaped
provider is required from the caller. Only the remaining ambient list is regular;
the coefficient list may have nonzero positive Koszul homology. The target uses
literally the same chosen family's coefficientList.get, including its order.

The frozen regularLeadingBlockIso supplies the native Tor symmetry, leading
change of rings, quotient Koszul resolution, and restriction of coefficient
homology. This file only instantiates that interface and transports the native
stalk points. The result is ambient-linear, not asserted coefficient-linear or
incidence-linear. The upstream symmetry and regular-family choices are retained;
no choice independence or naturality is claimed.

Software providers and literature scope are recorded in the separate report.
The ingredients use native Stacks regular-sequence Tor comparisons (062F, 00M3)
and Mathlib restriction composition, not a new homological foundation. This is
not the full exterior-composition, length, or Euler-coefficient theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback («C» := Scheme) X.hom Y.hom)
  (w : pullback («C» := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  (x : nativeExteriorIncidence X Y Z T z w hz hw)

local notation3 (prettyPrint := false) "fX" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "fY" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "fZ" => (SmoothSite.product Z T).hom
local notation3 (prettyPrint := false) "z'" => nativeExteriorPoint X Y T z hz
local notation3 (prettyPrint := false) "w'" => nativeExteriorPoint Y Z T w hw
local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "A" => correspondenceIntersectionAmbient fX fY fZ
local notation3 (prettyPrint := false) "P" => correspondenceSupportProduct fX fY fZ z' w'
local notation3 (prettyPrint := false) "V" => correspondenceTripleProduct fX fY fZ
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "QA" => exteriorAmbientParameterQuotient X Y Z T
local notation3 (prettyPrint := false) "a" =>
  correspondenceIncidenceAmbientInclusion fX fY fZ z' w'
local notation3 (prettyPrint := false) "b" =>
  correspondenceIncidenceToSupportProduct fX fY fZ z' w'
local notation3 (prettyPrint := false) "i" =>
  correspondenceSupportProductInclusion fX fY fZ z' w'
local notation3 (prettyPrint := false) "v" =>
  correspondenceIncidenceInclusion fX fY fZ z' w'
local notation3 (prettyPrint := false) "t" => correspondenceTripleInclusion fX fY fZ
local notation3 (prettyPrint := false) "j" =>
  nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "jA" => exteriorAmbientParameterInclusion X Y Z T
local notation3 (prettyPrint := false) "iQ" =>
  nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "l" => exteriorAmbientRemainingInclusion X Y Z T
local notation3 (prettyPrint := false) "Rₙ" =>
  correspondenceIncidenceAmbientStalk fX fY fZ z' w' x
local notation3 (prettyPrint := false) "R" => (A).presheaf.stalk (i (j (c x)))
local notation3 (prettyPrint := false) "D" => (Q).presheaf.stalk (c x)
local notation3 (prettyPrint := false) "f" =>
  (nativeExteriorAmbientParameterStalkMap X Y T z hz Z w hw (c x)).hom
local notation3 (prettyPrint := false) "g" =>
  (nativeExteriorRemainingAmbientStalkMap X Y T z hz Z w hw x).hom
local notation3 (prettyPrint := false) "φ" => ((i).stalkMap (j (c x))).hom
local notation3 (prettyPrint := false) "ψ" => ((j).stalkMap (c x)).hom

local notation3 (prettyPrint := false) "B" => (QA).presheaf.stalk (iQ (c x))
local notation3 (prettyPrint := false) "C" => (P).presheaf.stalk (j (c x))
local notation3 (prettyPrint := false) "L" => (V).presheaf.stalk (v x)
local notation3 (prettyPrint := false) "θ" => ((iQ).stalkMap (c x)).hom
local notation3 (prettyPrint := false) "e" =>
  nativeExteriorTorAmbientStalkIso X Y Z T z w hz hw x
local notation3 (prettyPrint := false) "κ" =>
  nativeExteriorTorCoefficientStalkMap X Y Z T z w hz hw x
local notation3 (prettyPrint := false) "F" =>
  nativeExteriorRemainingStalkFamily X Y T z hz Z w hw x
local notation3 (prettyPrint := false) "T'" =>
  correspondenceIncidenceAmbientTor fX fY fZ z' w' x
local notation3 (prettyPrint := false) "H" =>
  Koszul.seqComplexTensor (F).coefficientList.get (ModuleCat.of D D)

/-- The remaining coefficient complex is the literal ordered ambient-list image. -/
theorem nativeExteriorRemainingCoefficient_complex_eq :
    H = Koszul.seqComplexTensor (fun idx => (θ) ((F).ambientList.get idx))
      (ModuleCat.of D D) := by
  change Koszul.seqComplexTensor ((F).ambientList.map θ).get (ModuleCat.of D D) = _
  have aux {r₁ r₂ : ℕ} (hlen : r₁ = r₂) (f₁ : Fin r₁ → D) (f₂ : Fin r₂ → D)
      (hfun : HEq f₁ f₂) :
      Koszul.seqComplexTensor f₁ (ModuleCat.of D D) =
        Koszul.seqComplexTensor f₂ (ModuleCat.of D D) := by
    subst r₂
    cases hfun
    rfl
  apply aux (List.length_map (as := (F).ambientList) θ)
  apply (Fin.heq_fun_iff (List.length_map (as := (F).ambientList) θ)).mpr
  intro idx
  simp only [List.get_eq_getElem, List.getElem_map]

/-- Every native exterior ambient Tor degree reduces to the actual remaining coefficient
Koszul homology. The only linearity claimed is over the native ambient stalk. -/
def nativeExteriorAmbientTorRemainingKoszulIso (n : ℕ) :
    T' n ≅ (ModuleCat.restrictScalars κ).obj ((H).homology n) := by
  let G := nativeExteriorParameterStalkFamily X Y T z hz Z w hw (c x)
  let eBlock := ModuleCat.Tor.regularLeadingBlockIso f g φ ψ θ
    (nativeExteriorParameter_stalkRingSquare X Y T z hz Z w hw (c x))
    (nativeExteriorAmbientParameterStalkMap_surjective X Y T z hz Z w hw (c x))
    (nativeExteriorRemainingAmbientStalkMap_surjective X Y T z hz Z w hw x)
    ((j).stalkMap_surjective (c x)) G.ambientList (F).ambientList
    G.ambient_regular G.ambient_kernel G.coefficient_regular.toIsWeaklyRegular
    G.coefficient_kernel (F).ambient_regular (F).ambient_kernel n
  let eList : (Koszul.seqComplexTensor (fun idx => (θ) ((F).ambientList.get idx))
      (ModuleCat.of D D)).homology n ≅ (H).homology n :=
    eqToIso (congrArg (fun K => K.homology n)
      (nativeExteriorRemainingCoefficient_complex_eq X Y Z T z w hz hw x).symm)
  let eK : ((Tor (ModuleCat R) n).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))).obj
        ((ModuleCat.restrictScalars ((g).comp f)).obj (ModuleCat.of L L)) ≅
      (ModuleCat.restrictScalars ((ψ).comp φ)).obj ((H).homology n) :=
    eBlock ≪≫ (ModuleCat.restrictScalars ((ψ).comp φ)).mapIso eList
  exact correspondenceIncidenceAmbientTorIsoOfSupportPoint fX fY fZ z' w' x
      (j (c x)) (nativeExteriorTor_supportPoint X Y Z T z w hz hw x) ((g).comp f)
      (nativeExteriorTor_tripleStalkMap X Y Z T z w hz hw x) n ≪≫
    (ModuleCat.restrictScalars (e).hom.hom).mapIso eK ≪≫
    (ModuleCat.restrictScalarsComp'App (e).hom.hom ((ψ).comp φ) κ rfl
      ((H).homology n)).symm

end Stacks.Chow

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.AmbientTorPointTransport
public import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterStalkMaps
public import Colib.AlgebraicGeometry.Correspondences.Exterior.RemainingStalkFamily

/-!
# Actual ambient Tor points and scalar maps for the exterior incidence

SOURCE_ONLY_UNCOMPILED. The native ambient stalk is at the image of the full
incidence in the four-factor ambient. The regular-leading-block comparison uses
instead the equal point obtained through the coefficient parameter quotient.
Their equality is retained as a stalk isomorphism. The native support point is
likewise identified with the actual image under the parameter inclusion.

The triple scalar map is the composite of the actual ambient parameter quotient
and actual remaining quotient, after this ambient point transport. The proof
uses the equality of the actual triple inclusion with the two-stage inclusion,
not definitional equality of their stalk maps. The ambient-to-coefficient map
also factors the actual ambient-to-incidence map. No larger scalar linearity is
asserted and no Tor comparison is assumed.

Native providers: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/AlgebraicGeometry/Scheme.lean:918-948, and the frozen exterior parameter
and remaining-diagonal geometry. Exact source hashes are recorded separately.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
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

/-- The parameter quotient gives the native support point, with its equality explicit. -/
theorem nativeExteriorTor_supportPoint : j (c x) = b x :=
  congrArg (fun m : I' ⟶ P => m x)
    (nativeExteriorIncidenceToCoefficientQuotient_inclusion X Y Z T z w hz hw)

/-- Identify the native ambient stalk with the actual leading-block ambient stalk. -/
def nativeExteriorTorAmbientStalkIso : Rₙ ≅ R :=
  correspondenceIncidenceAmbientStalkIsoOfSupportPoint fX fY fZ z' w' x
    (j (c x)) (nativeExteriorTor_supportPoint X Y Z T z w hz hw x)

/-- The native triple scalar map is exactly the two quotient maps after point transport. -/
theorem nativeExteriorTor_tripleStalkMap :
    ((t).stalkMap (v x)).hom = ((g).comp f).comp
      (nativeExteriorTorAmbientStalkIso X Y Z T z w hz hw x).hom.hom := by
  have aux (p : A) (q : QA) (y : V)
      (ha : t y = p) (hp : p = jA q) (hq : q = l y) :
      (t).stalkMap y = ((A).presheaf.stalkCongr (.of_eq ha)).hom ≫
        (((A).presheaf.stalkCongr (.of_eq hp)).hom ≫ (jA).stalkMap q) ≫
          (((QA).presheaf.stalkCongr (.of_eq hq)).hom ≫ (l).stalkMap y) := by
    revert ha
    subst q
    subst p
    intro ha
    simpa only [Scheme.Hom.stalkMap_comp, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, Category.assoc] using
      Scheme.Hom.stalkMap_congr_hom t (l ≫ jA)
        (exteriorAmbientRemainingInclusion_parameterInclusion X Y Z T).symm y
  exact congrArg CommRingCat.Hom.hom
    (aux (i (j (c x))) (iQ (c x)) (v x)
      ((correspondenceIncidence_ambient_point_eq fX fY fZ z' w' x).trans
        (congrArg i (nativeExteriorTor_supportPoint X Y Z T z w hz hw x).symm))
      (nativeExteriorParameter_ambientPoint X Y T z hz Z w hw (c x))
      (nativeExteriorRemaining_ambientPoint X Y T z hz Z w hw x))

/-- The actual native ambient action on the remaining coefficient ring. -/
def nativeExteriorTorCoefficientStalkMap : Rₙ →+* D :=
  (ψ).comp ((φ).comp (nativeExteriorTorAmbientStalkIso X Y Z T z w hz hw x).hom.hom)

/-- This coefficient action followed by the full incidence quotient is the native action. -/
theorem nativeExteriorTorCoefficientStalkMap_incidence :
    ((c).stalkMap x).hom.comp (nativeExteriorTorCoefficientStalkMap X Y Z T z w hz hw x) =
      ((a).stalkMap x).hom := by
  have h : a = c ≫ j ≫ i := by
    rw [← Category.assoc, nativeExteriorIncidenceToCoefficientQuotient_inclusion]
    exact correspondenceIncidence_ambient_comm fX fY fZ z' w'
  have he := Scheme.Hom.stalkMap_congr_hom a (c ≫ j ≫ i) h x
  simpa only [nativeExteriorTorCoefficientStalkMap, nativeExteriorTorAmbientStalkIso,
    correspondenceIncidenceAmbientStalkIsoOfSupportPoint, Scheme.Hom.stalkMap_comp,
    Category.assoc, CommRingCat.hom_comp, RingHom.comp_assoc] using
      (congrArg CommRingCat.Hom.hom he).symm

end Stacks.Chow

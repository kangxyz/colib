/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.RemainingStalkFamily
public import Colib.AlgebraicGeometry.Correspondences.Composition.OriginalKoszulPointTransport

/-!
# Actual original Tor stalk points and coefficient scalars

SOURCE_ONLY_UNCOMPILED. At an actual exterior incidence point x, C₀ is the
original support stalk at q(c(x)), while the accepted original Tor comparison
uses the support stalk at b₀(π(x)). Their equality is the saved quotient-square
point equality. The remaining Y point also agrees with the original ambient
middle point; its equality uses the saved remaining base point and original
ambient incidence equality. Neither equality is treated as definitional.

The square below identifies the actual remaining coefficient map u₀ with the
original ambient-to-support map conjugated by those two stalkCongr maps. It is
an equality of ring homomorphisms, so it preserves every entry of the ordered
list, not only the generated ideal. The Tor coefficient action is explicitly
η₀ followed by the already existing E₀ action. No support flatness is used.

Inputs are the frozen, source-only RemainingStalkFamily and QuotientIncidence
packets. Native stalk transport and composition are from Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/AlgebraicGeometry/Scheme.lean:918-948. This is a pointwise scalar
identification, not a new Tor base-change or naturality theorem.
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
local notation3 (prettyPrint := false) "A₀" =>
  correspondenceIntersectionAmbient X.hom Y.hom Z.hom
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "q" =>
  nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw
local notation3 (prettyPrint := false) "π" => nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "iQ" =>
  nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "r" => exteriorAmbientRemainingPair X Y Z T
local notation3 (prettyPrint := false) "r₀" => nativeOriginalCoefficientMiddlePair X Y z Z w
local notation3 (prettyPrint := false) "b₀" =>
  correspondenceIncidenceToSupportProduct X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "a₀" =>
  correspondenceIncidenceAmbientInclusion X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "i₀" =>
  correspondenceSupportProductInclusion X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "m₀" => correspondenceMiddlePair X.hom Y.hom Z.hom
local notation3 (prettyPrint := false) "C₀" => (P₀).presheaf.stalk (q (c x))
local notation3 (prettyPrint := false) "U" =>
  (pullback Y.hom Y.hom).presheaf.stalk (r (iQ (c x)))
local notation3 (prettyPrint := false) "T₀" =>
  correspondenceIncidenceAmbientTor X.hom Y.hom Z.hom z w (π x)
local notation3 (prettyPrint := false) "η₀" =>
  (nativeExteriorRemainingOriginalIncidenceStalkMap X Y T z hz Z w hw x).hom

/-- The remaining Y point is the actual original ambient middle point. -/
theorem nativeExteriorOriginalTor_middlePoint : r (iQ (c x)) = m₀ (a₀ (π x)) := by
  calc
    r (iQ (c x)) = r₀ (q (c x)) :=
      nativeExteriorRemaining_basePoint X Y T z hz Z w hw x
    _ = r₀ (b₀ (π x)) := congrArg r₀
      (nativeExteriorIncidenceQuotient_point X Y Z T z w hz hw x).symm
    _ = m₀ (a₀ (π x)) := by
      simpa only [nativeOriginalCoefficientMiddlePair, Scheme.Hom.comp_apply] using
        congrArg m₀
          (correspondenceIncidence_ambient_point_eq X.hom Y.hom Z.hom z w (π x)).symm

/-- The actual support-stalk equality used to restrict the original Tor action. -/
def nativeExteriorOriginalTorSupportStalkIso :
    C₀ ≅ (P₀).presheaf.stalk (b₀ (π x)) :=
  (P₀).presheaf.stalkCongr
    (.of_eq (nativeExteriorIncidenceQuotient_point X Y Z T z w hz hw x).symm)

/-- The actual remaining-middle stalk equality, with the original ambient endpoint. -/
def nativeExteriorOriginalTorMiddleStalkIso :
    U ≅ (pullback Y.hom Y.hom).presheaf.stalk (m₀ (a₀ (π x))) :=
  (pullback Y.hom Y.hom).presheaf.stalkCongr
    (.of_eq (nativeExteriorOriginalTor_middlePoint X Y Z T z w hz hw x))

/-- Both actual routes from the remaining Y stalk to the original support stalk agree. -/
theorem nativeExteriorOriginalTor_middleSquare :
    nativeExteriorRemainingOriginalStalkMap X Y T z hz Z w hw x ≫
        (nativeExteriorOriginalTorSupportStalkIso X Y Z T z w hz hw x).hom =
      (nativeExteriorOriginalTorMiddleStalkIso X Y Z T z w hz hw x).hom ≫
        (m₀).stalkMap (a₀ (π x)) ≫
          CommRingCat.ofHom
            (correspondenceIncidenceSupportStalkMap X.hom Y.hom Z.hom z w (π x)) := by
  have aux (d d' : P₀) (a : A₀) (y : pullback (C := Scheme) Y.hom Y.hom)
      (hd : d = d') (ha : a = i₀ d') (hy : y = r₀ d) (hy' : y = m₀ a) :
      (((pullback Y.hom Y.hom).presheaf.stalkCongr (.of_eq hy)).hom ≫
          (r₀).stalkMap d) ≫ ((P₀).presheaf.stalkCongr (.of_eq hd)).hom =
        ((pullback Y.hom Y.hom).presheaf.stalkCongr (.of_eq hy')).hom ≫
          (m₀).stalkMap a ≫ ((A₀).presheaf.stalkCongr (.of_eq ha)).hom ≫
            (i₀).stalkMap d' := by
    subst d'
    subst a
    subst y
    simp [nativeOriginalCoefficientMiddlePair, Scheme.Hom.stalkMap_comp,
      TopCat.Presheaf.stalkCongr]
  simpa only [nativeExteriorRemainingOriginalStalkMap,
    nativeExteriorOriginalTorSupportStalkIso, nativeExteriorOriginalTorMiddleStalkIso,
    correspondenceIncidenceSupportStalkMap, CommRingCat.ofHom_hom, Category.assoc] using
      aux (q (c x)) (b₀ (π x)) (a₀ (π x)) (r (iQ (c x)))
        (nativeExteriorIncidenceQuotient_point X Y Z T z w hz hw x).symm
        (correspondenceIncidence_ambient_point_eq X.hom Y.hom Z.hom z w (π x))
        (nativeExteriorRemaining_basePoint X Y T z hz Z w hw x)
        (nativeExteriorOriginalTor_middlePoint X Y Z T z w hz hw x)

/-- Original ambient middle scalars, transported to precisely U and C₀. -/
def nativeExteriorOriginalTorMiddleStalkMap : U →+* C₀ :=
  (((nativeExteriorOriginalTorMiddleStalkIso X Y Z T z w hz hw x).hom ≫
    (m₀).stalkMap (a₀ (π x)) ≫
      CommRingCat.ofHom
        (correspondenceIncidenceSupportStalkMap X.hom Y.hom Z.hom z w (π x))) ≫
          (nativeExteriorOriginalTorSupportStalkIso X Y Z T z w hz hw x).inv).hom

/-- The transported public comparison uses the literal saved original coefficient map. -/
theorem nativeExteriorOriginalTorMiddleStalkMap_eq :
    nativeExteriorOriginalTorMiddleStalkMap X Y Z T z w hz hw x =
      (nativeExteriorRemainingOriginalStalkMap X Y T z hz Z w hw x).hom := by
  have hs := congrArg
    (fun f => f ≫ (nativeExteriorOriginalTorSupportStalkIso X Y Z T z w hz hw x).inv)
    (nativeExteriorOriginalTor_middleSquare X Y Z T z w hz hw x)
  simpa only [nativeExteriorOriginalTorMiddleStalkMap, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] using (congrArg CommRingCat.Hom.hom hs).symm

/-- C₀ acts through the actual η₀ and the existing original-incidence native Tor action. -/
@[instance_reducible]
def nativeExteriorOriginalTorCoefficientModule (n : ℕ) : Module C₀ (T₀ n) := by
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  exact Module.compHom (T₀ n) η₀

/-- The coefficient action retains the original full-incidence scalar dictionary. -/
theorem nativeExteriorOriginalTorCoefficientModule_smul (n : ℕ) (a : C₀) (t : T₀ n) :
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    a • t = (η₀) a • t := rfl

/-- The literal C₀ action forms the expected tower with the existing E₀ action. -/
theorem nativeExteriorOriginalTorCoefficientScalarTower (n : ℕ) :
    let E₀ := (correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk (π x)
    let : Algebra C₀ E₀ := (η₀).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    IsScalarTower C₀ E₀ (T₀ n) := by
  let E₀ := (correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk (π x)
  let : Algebra C₀ E₀ := (η₀).toAlgebra
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
  exact IsScalarTower.of_compHom C₀ E₀ (T₀ n)

end Stacks.Chow

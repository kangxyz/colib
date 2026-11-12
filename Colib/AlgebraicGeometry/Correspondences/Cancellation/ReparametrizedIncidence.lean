/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedIncidence.IncidenceIso
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedIncidence.SupportProduct
public import Colib.AlgebraicGeometry.Correspondences.Exterior.RemainingDiagonal

/-!
# The common coefficient product for a reparametrized incidence

The graph insertion is the parameter-diagonal quotient of the actual
support product. The remaining middle pair retains the original projections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (U X Z T : SmoothSite (Spec (.of k)))
  (z : pullback (C := Scheme) (SmoothSite.product U T).hom (SmoothSite.product X T).hom)
  (w : pullback (C := Scheme) (SmoothSite.product X T).hom (SmoothSite.product Z T).hom)
  {Q P : Scheme.{u}} (p : Q ⟶ X.left) (r : P ⟶ X.left) (l : P ⟶ T.left)
  (hl : r ≫ X.hom = l ≫ T.hom)
  (eQ : pullback (C := Scheme) (p ≫ X.hom) T.hom ≅ (integralComponentAt z).subscheme)
  (eP : P ≅ (integralComponentAt w).subscheme)
  (hQ : eQ.hom ≫ ((integralComponentAt z).subschemeι ≫
    pullback.snd (SmoothSite.product U T).hom (SmoothSite.product X T).hom) =
      pullbackParameterExtensionMap p X.hom T.hom)
  (hP : eP.hom ≫ ((integralComponentAt w).subschemeι ≫
    pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom) =
      pullback.lift r l hl)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product U T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Z T).hom
local notation3 (prettyPrint := false) "a" => reparametrizedLeftSupportMiddle U X T z
local notation3 (prettyPrint := false) "b" => reparametrizedRightSupportMiddle X Z T w
local notation3 (prettyPrint := false) "aS" => reparametrizedLeftSupportBase U X T z
local notation3 (prettyPrint := false) "bS" => reparametrizedRightSupportBase X Z T w
local notation3 (prettyPrint := false) "pBase" => reparametrizedFreeSupportBase X T p
local notation3 (prettyPrint := false) "pS" => p ≫ X.hom
local notation3 (prettyPrint := false) "rS" => r ≫ X.hom
local notation3 (prettyPrint := false) "D" => pullback (C := Scheme) pS rS
local notation3 (prettyPrint := false) "C" => correspondenceSupportProduct f g h z w
local notation3 (prettyPrint := false) "i" => correspondenceSupportProductInclusion f g h z w
local notation3 (prettyPrint := false) "A" => exteriorAmbientParameterQuotient U X Z T
local notation3 (prettyPrint := false) "j" => exteriorAmbientParameterInclusion U X Z T

set_option maxHeartbeats 600000 in
-- The map composes the nested support pullback with its literal product comparison.
/-- The actual insertion of the graph parameter into the native support product. -/
def reparametrizedCoefficientInclusion : D ⟶ C :=
  let eC : pullback («C» := Scheme) pBase rS ≅ pullback («C» := Scheme) aS bS :=
    @reparametrizedSupportProductIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
  pullbackParameterGraphInclusion pS rS T.hom l hl.symm ≫ eC.hom

local notation3 (prettyPrint := false) "c" =>
  reparametrizedCoefficientInclusion U X Z T z w p r l hl eQ eP hQ hP

set_option maxHeartbeats 600000 in
-- Transporting the graph square reduces both descriptions of the full support product.
/-- The graph insertion is the full inverse image of the parameter diagonal. -/
theorem reparametrizedCoefficient_isPullback :
    IsPullback c (pullback.snd pS rS ≫ l)
      (i ≫ exteriorAmbientParameterPair U X Z T) (pullback.diagonal T.hom) := by
  let eC : pullback («C» := Scheme) pBase rS ≅ pullback («C» := Scheme) aS bS :=
    @reparametrizedSupportProductIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
  refine (pullbackParameterGraph_isPullback pS rS T.hom l hl.symm).of_iso
    (Iso.refl _) eC (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_ (by simp)
  · exact (Category.id_comp c).symm
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (reparametrizedSupportProductIso_parameterPair U X Z T z w p r l hl eQ eP hQ hP).symm

set_option maxHeartbeats 600000 in
-- The two projections are elaborated on the ambient and coefficient graph pullbacks.
/-- The common product maps to the actual ambient parameter quotient. -/
def reparametrizedCoefficientQuotientMap : D ⟶ A :=
  pullback.lift (pullback.snd pS rS ≫ l) (c ≫ i) (by
    simpa only [Category.assoc] using
      (reparametrizedCoefficient_isPullback U X Z T z w p r l hl eQ eP hQ hP).w.symm)

local notation3 (prettyPrint := false) "d" =>
  reparametrizedCoefficientQuotientMap U X Z T z w p r l hl eQ eP hQ hP

@[reassoc (attr := simp)]
theorem reparametrizedCoefficientQuotientMap_ambient : d ≫ j = c ≫ i :=
  pullback.lift_snd _ _ _

/-- The ambient and coefficient graph quotients are Cartesian. -/
theorem reparametrizedCoefficientQuotientMap_isPullback :
    IsPullback d c j i := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst (pullback.diagonal T.hom) (exteriorAmbientParameterPair U X Z T))
    (h₂₂ := exteriorAmbientParameterPair U X Z T)
  · have hd : d ≫ pullback.fst (pullback.diagonal T.hom)
        (exteriorAmbientParameterPair U X Z T) = pullback.snd pS rS ≫ l :=
      pullback.lift_fst _ _ _
    simpa only [hd] using
      (reparametrizedCoefficient_isPullback U X Z T z w p r l hl eQ eP hQ hP).flip
  · exact reparametrizedCoefficientQuotientMap_ambient U X Z T z w p r l hl eQ eP hQ hP
  · exact exteriorAmbientParameter_isPullback U X Z T

/-- The actual middle pair on the common product. -/
def reparametrizedRemainingMiddlePair : D ⟶ pullback X.hom X.hom :=
  pullback.map pS rS X.hom X.hom p r (𝟙 _) (by simp) (by simp)

/-- Both remaining middle coordinates are independent of the parameter map. -/
theorem reparametrizedCoefficientQuotientMap_remainingPair :
    d ≫ exteriorAmbientRemainingPair U X Z T = reparametrizedRemainingMiddlePair X p r := by
  let eC : pullback («C» := Scheme) pBase rS ≅ pullback («C» := Scheme) aS bS :=
    @reparametrizedSupportProductIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
  let j₀ := pullbackParameterGraphInclusion pS rS T.hom l hl.symm
  have hL : eC.hom ≫ pullback.fst aS bS = pullback.fst pBase rS ≫ eQ.hom :=
    reparametrizedSupportProductIso_fst U X Z T z w p r l hl eQ eP hQ hP
  have hR : eC.hom ≫ pullback.snd aS bS = pullback.snd pBase rS ≫ eP.hom :=
    reparametrizedSupportProductIso_snd U X Z T z w p r l hl eQ eP hQ hP
  have hleft : eC.hom ≫ i ≫ exteriorAmbientOldMiddlePair U X Z T ≫
      pullback.fst X.hom X.hom = pullback.fst pBase rS ≫ pullback.fst pS T.hom ≫ p := by
    rw [exteriorAmbientOldMiddlePair_fst, correspondenceSupportProductInclusion_fst_assoc]
    change eC.hom ≫ pullback.fst aS bS ≫ a ≫ pullback.fst X.hom T.hom = _
    rw [reassoc_of% hL]
    exact congrArg (pullback.fst pBase rS ≫ ·)
      (reparametrized_left_projection U X T z p eQ hQ)
  have hright : eC.hom ≫ i ≫ exteriorAmbientOldMiddlePair U X Z T ≫
      pullback.snd X.hom X.hom = pullback.snd pBase rS ≫ r := by
    rw [exteriorAmbientOldMiddlePair_snd, correspondenceSupportProductInclusion_snd_assoc]
    change eC.hom ≫ pullback.snd aS bS ≫ b ≫ pullback.fst X.hom T.hom = _
    rw [reassoc_of% hR]
    exact congrArg (pullback.snd pBase rS ≫ ·)
      (reparametrized_right_projection X Z T w r l hl eP hP)
  apply pullback.hom_ext («f» := X.hom) («g» := X.hom)
  · simp only [exteriorAmbientRemainingPair, Category.assoc,
      reparametrizedCoefficientQuotientMap_ambient_assoc, reparametrizedRemainingMiddlePair,
      pullback.lift_fst]
    change j₀ ≫ (eC.hom ≫ i ≫ exteriorAmbientOldMiddlePair U X Z T ≫
      pullback.fst X.hom X.hom) = pullback.fst pS rS ≫ p
    rw [hleft]
    exact (pullbackParameterGraphInclusion_first_assoc pS rS T.hom l hl.symm p)
  · simp only [exteriorAmbientRemainingPair, Category.assoc,
      reparametrizedCoefficientQuotientMap_ambient_assoc, reparametrizedRemainingMiddlePair,
      pullback.lift_snd]
    change j₀ ≫ (eC.hom ≫ i ≫ exteriorAmbientOldMiddlePair U X Z T ≫
      pullback.snd X.hom X.hom) = pullback.snd pS rS ≫ r
    rw [hright]
    exact (pullbackParameterGraphInclusion_second_assoc pS rS T.hom l hl.symm r)

/-- The original incidence lies in the common product by its two projections. -/
abbrev reparametrizedIncidenceToProduct : pullback p r ⟶ D :=
  pullback.mapDesc p r X.hom

local notation3 (prettyPrint := false) "v" => reparametrizedIncidenceToProduct X p r

/-- The common coefficient point lies on the literal original middle diagonal. -/
theorem reparametrizedIncidenceToProduct_middleDiagonal :
    v ≫ reparametrizedRemainingMiddlePair X p r =
      pullback.fst p r ≫ p ≫ pullback.diagonal X.hom := by
  apply pullback.hom_ext («f» := X.hom) («g» := X.hom)
  · simp [reparametrizedIncidenceToProduct, reparametrizedRemainingMiddlePair,
      pullback.mapDesc, pullback.map, Category.assoc]
  · simpa [reparametrizedIncidenceToProduct, reparametrizedRemainingMiddlePair,
      pullback.mapDesc, pullback.map, Category.assoc] using
      (pullback.condition («f» := p) («g» := r)).symm

/-- The incidence and graph-insertion maps agree on the full native support
product. This identifies the actual point used in the quotient stalk. -/
@[reassoc]
theorem reparametrizedIncidenceIso_coefficient :
    let e : pullback («C» := Scheme) p r ≅ pullback («C» := Scheme) a b :=
      @reparametrizedIncidenceIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    e.hom ≫ correspondenceIncidenceToSupportProduct f g h z w = v ≫ c := by
  have hvL : v ≫ pullback.fst pS rS = pullback.fst p r :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hvR : v ≫ pullback.snd pS rS = pullback.snd p r :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hGraphFst :
      pullbackParameterGraphInclusion pS rS T.hom l hl.symm ≫
          pullback.fst pBase rS ≫ pullback.fst pS T.hom =
        pullback.fst pS rS := pullbackParameterGraphInclusion_first pS rS T.hom l hl.symm
  have hGraphParameter :
      pullbackParameterGraphInclusion pS rS T.hom l hl.symm ≫
          pullback.fst pBase rS ≫ pullback.snd pS T.hom =
        pullback.snd pS rS ≫ l := pullbackParameterGraphInclusion_parameter pS rS T.hom l hl.symm
  have hGraphSnd :
      pullbackParameterGraphInclusion pS rS T.hom l hl.symm ≫ pullback.snd pBase rS =
        pullback.snd pS rS := pullbackParameterGraphInclusion_second pS rS T.hom l hl.symm
  apply pullback.hom_ext («f» := aS) («g» := bS)
  · simp only [Category.assoc, correspondenceIncidenceToSupportProduct_fst,
      reparametrizedCoefficientInclusion, reparametrizedSupportProductIso_fst]
    apply (cancel_mono (eQ).inv).mp
    apply pullback.hom_ext («f» := pS) («g» := T.hom)
    · simp only [Category.assoc, Iso.hom_inv_id_assoc, reparametrizedIncidenceIso_fst,
        hGraphFst, hvL]
    · simp only [Category.assoc, Iso.hom_inv_id_assoc, reparametrizedIncidenceIso_parameter,
        hGraphParameter, reassoc_of% hvR]
  · simp only [Category.assoc, correspondenceIncidenceToSupportProduct_snd,
      reparametrizedCoefficientInclusion, reparametrizedSupportProductIso_snd,
      reparametrizedIncidenceIso_snd, reassoc_of% hGraphSnd, reassoc_of% hvR]

set_option maxHeartbeats 600000 in
-- Cancelling the ambient inclusion compares maps between nested scheme pullbacks.
/-- The common incidence has the actual triple-product image in the ambient
parameter quotient. -/
theorem reparametrizedIncidenceIso_ambientQuotient :
    let e : pullback («C» := Scheme) p r ≅ pullback («C» := Scheme) a b :=
      @reparametrizedIncidenceIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    v ≫ d = e.hom ≫ correspondenceIncidenceInclusion f g h z w ≫
      exteriorAmbientRemainingInclusion U X Z T := by
  let e : pullback («C» := Scheme) p r ≅ pullback («C» := Scheme) a b :=
    @reparametrizedIncidenceIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
  change v ≫ d = e.hom ≫ correspondenceIncidenceInclusion f g h z w ≫
    exteriorAmbientRemainingInclusion U X Z T
  apply (cancel_mono j).mp
  simp only [Category.assoc, reparametrizedCoefficientQuotientMap_ambient,
    exteriorAmbientRemainingInclusion_parameterInclusion]
  rw [← reparametrizedIncidenceIso_coefficient_assoc]
  exact congrArg (e.hom ≫ ·) (correspondenceIncidence_ambient_comm f g h z w).symm

end Stacks.Chow

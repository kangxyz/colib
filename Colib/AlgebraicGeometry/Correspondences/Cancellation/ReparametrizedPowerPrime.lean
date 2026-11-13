/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedPrimeSupports
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedTorCycle
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.AmbientGraph
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Parameters

/-!
# Power-parameter reparametrization of a prime transfer composition

The actual closed power graph commutes with composition by the
exterior of a prime transfer and the torus identity. The outer maps
retain the old target and old source torus, and their new parameter
uses the same two original units.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable {k : Type u} [Field k]

variable (U X Y : SmoothSite (Spec (.of k)))
  (z : pullback (C := Scheme) U.hom X.hom)
  (hz : IsFiniteCorrespondencePoint U.hom X.hom z)
  (w : pullback (C := Scheme)
    (product X (multiplicativeGroupObject (Spec (.of k)))).hom
    (product Y (multiplicativeGroupObject (Spec (.of k)))).hom)
  (hw : IsFiniteCorrespondencePoint
    (product X (multiplicativeGroupObject (Spec (.of k)))).hom
    (product Y (multiplicativeGroupObject (Spec (.of k)))).hom w)
  (n : ℕ) (u₀ : (Γ((product Y (multiplicativeGroupObject (Spec (.of k)))).left, ⊤))ˣ)

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "G(" X ")" => product X T
local notation "V(" Y ")" => torusPowerCutRetainedTarget k Y

local notation3 (prettyPrint := false) "f" => (G(U)).hom
local notation3 (prettyPrint := false) "g" => (G(X)).hom
local notation3 (prettyPrint := false) "h" => (G(Y)).hom
local notation3 (prettyPrint := false) "h'" => (V(Y)).hom
local notation3 (prettyPrint := false) "zT" => nativeExteriorPoint U X T z hz
local notation3 (prettyPrint := false) "hzT" => nativeExteriorPoint_admissible U X T z hz
local notation3 (prettyPrint := false) "J" => torusPowerParameterAmbientGraph k (X := U) n u₀
local notation3 (prettyPrint := false) "J₀" => torusPowerParameterAmbientGraph k (X := X) n u₀
local notation3 (prettyPrint := false) "w'" => J₀ w

set_option maxHeartbeats 900000 in
-- The two incidence isomorphisms retain all original and new parameter projections.
/-- The retained ambient graph intertwines the exact native Tor cycle of
two prime correspondences with the reparametrized right correspondence. -/
theorem torusPowerParameter_primeComposition_val
    (hw' : IsFiniteCorrespondencePoint g h' w') :
    finiteCyclePushforward J (incidenceTorCorrespondence f g h zT w hzT hw).val =
      (incidenceTorCorrespondence f g h' zT w' hzT hw').val := by
  let Q := (integralComponentAt z).subscheme
  let P := (integralComponentAt w).subscheme
  let : IsIntegral P := isIntegral_integralComponentAt w
  let j : P ⟶ pullback g h := (integralComponentAt w).subschemeι
  let j' : P ⟶ pullback g h' := j ≫ J₀
  let : IsClosedImmersion j :=
    inferInstanceAs (IsClosedImmersion (integralComponentAt w).subschemeι)
  let : IsClosedImmersion J₀ :=
    torusPowerParameterAmbientGraph_isClosedImmersion k (X := X) (Y := Y) n u₀
  let : IsClosedImmersion j' :=
    MorphismProperty.comp_mem (@IsClosedImmersion) j J₀ inferInstance inferInstance
  let gP : P ⟶ (G(X)).left := j ≫ pullback.fst g h
  let aP : (Γ(P, ⊤))ˣ := torusPowerParameterUnit k (X := X) (Y := Y) n u₀ j
  let p : Q ⟶ X.left := exteriorSupportTargetProjection U X (integralComponentAt z)
  let q : Q ⟶ U.left := exteriorSupportSourceProjection U X (integralComponentAt z)
  let r : P ⟶ X.left := torusSupportBaseProjection k (X := X) gP
  let l₁ : P ⟶ (T).left := gP ≫ pullback.snd X.hom (T).hom
  let l₂ : P ⟶ (T).left := (j' ≫ pullback.fst g h') ≫ pullback.snd X.hom (T).hom
  have hbase₂ : (j' ≫ pullback.fst g h') ≫ pullback.fst X.hom (T).hom = r := by
    change ((j ≫ J₀) ≫ pullback.fst g h') ≫ pullback.fst X.hom (T).hom =
      (j ≫ pullback.fst g h) ≫ pullback.fst X.hom (T).hom
    simp only [Category.assoc, torusPowerParameterAmbientGraph_source]
  have hl₁ : r ≫ X.hom = l₁ ≫ (T).hom := by
    change (gP ≫ pullback.fst X.hom (T).hom) ≫ X.hom =
      (gP ≫ pullback.snd X.hom (T).hom) ≫ (T).hom
    simp only [Category.assoc, pullback.condition]
  have hl₂ : r ≫ X.hom = l₂ ≫ (T).hom := by
    rw [← hbase₂]
    simp only [l₂, Category.assoc, pullback.condition]
  let eQ : pullback (p ≫ X.hom) (T).hom ≅ (integralComponentAt zT).subscheme :=
    reparametrizedExteriorSupportIso U X T z hz
  have hjη : j' (genericPoint P) = w' := by
    change J₀ (j (genericPoint P)) = J₀ w
    exact congrArg J₀ (genericPointOf_integralComponentAt w)
  let eP : P ≅ (integralComponentAt w').subscheme := closedIntegralSupportIsoOfEq j' w' hjη
  have hj' : eP.hom ≫ (integralComponentAt w').subschemeι = j' :=
    closedIntegralSupportIsoOfEq_hom_inclusion j' w' hjη
  have hQ := reparametrizedExteriorSupportIso_target U X T z hz
  have hP₁ : (Iso.refl P).hom ≫ ((integralComponentAt w).subschemeι ≫ pullback.fst g h) =
      pullback.lift r l₁ hl₁ := by
    change (𝟙 P) ≫ gP = _
    rw [Category.id_comp]
    apply pullback.hom_ext («f» := X.hom) («g» := (T).hom)
    · exact (pullback.lift_fst r l₁ hl₁).symm
    · exact (pullback.lift_snd r l₁ hl₁).symm
  have hP₂ : eP.hom ≫ ((integralComponentAt w').subschemeι ≫ pullback.fst g h') =
      pullback.lift r l₂ hl₂ := by
    rw [← Category.assoc, hj']
    apply pullback.hom_ext («f» := X.hom) («g» := (T).hom)
    · rw [pullback.lift_fst, hbase₂]
    · exact (pullback.lift_snd r l₂ hl₂).symm
  let I := pullback (C := Scheme) p r
  let e₁ : I ≅ correspondenceIncidence f g h zT w :=
    @reparametrizedIncidenceIso k _ U X Y T zT w Q P p r l₁ hl₁ eQ (Iso.refl P) hQ hP₁
  let e₂ : I ≅ correspondenceIncidence f g h' zT w' :=
    @reparametrizedIncidenceIso k _ U X (G(Y)) T zT w' Q P p r l₂ hl₂ eQ eP hQ hP₂
  let F₁ : I ⟶ pullback f h := e₁.hom ≫ correspondenceIncidenceMap f g h zT w
  let F₂ : I ⟶ pullback f h' := e₂.hom ≫ correspondenceIncidenceMap f g h' zT w'
  have hQ₁ := reparametrizedExteriorSupportIso_source_fst U X T z hz
  have hQ₂ := reparametrizedExteriorSupportIso_source_snd U X T z hz
  have hbase₁ : F₁ ≫ pullback.fst f h ≫ pullback.fst U.hom (T).hom =
      pullback.fst p r ≫ q := by
    simpa only [F₁, Category.assoc, correspondenceIncidenceMap_fst_assoc] using
      reparametrizedIncidenceIso_left_fst U X Y T zT w p r l₁ hl₁ eQ
        (Iso.refl P) hQ hP₁ q hQ₁
  have hbase₂' : F₂ ≫ pullback.fst f h' ≫ pullback.fst U.hom (T).hom =
      pullback.fst p r ≫ q := by
    simpa only [F₂, Category.assoc, correspondenceIncidenceMap_fst_assoc] using
      reparametrizedIncidenceIso_left_fst U X (G(Y)) T zT w' p r l₂ hl₂ eQ eP hQ hP₂ q hQ₁
  have htorus₁ : F₁ ≫ pullback.fst f h ≫ pullback.snd U.hom (T).hom =
      pullback.snd p r ≫ l₁ := by
    simpa only [F₁, Category.assoc, correspondenceIncidenceMap_fst_assoc] using
      reparametrizedIncidenceIso_left_snd U X Y T zT w p r l₁ hl₁ eQ (Iso.refl P) hQ hP₁ hQ₂
  have htorus₂ : F₂ ≫ pullback.fst f h' ≫ pullback.snd U.hom (T).hom =
      pullback.snd p r ≫ l₂ := by
    simpa only [F₂, Category.assoc, correspondenceIncidenceMap_fst_assoc] using
      reparametrizedIncidenceIso_left_snd U X (G(Y)) T zT w' p r l₂ hl₂ eQ eP hQ hP₂ hQ₂
  have htarget₁ : F₁ ≫ pullback.snd f h = pullback.snd p r ≫ j ≫ pullback.snd g h := by
    simpa only [F₁, Category.assoc, correspondenceIncidenceMap_snd,
      Iso.refl_hom, Category.id_comp] using
      reparametrizedIncidenceIso_right U X Y T zT w p r l₁ hl₁ eQ (Iso.refl P) hQ hP₁
  have htarget₂ : F₂ ≫ pullback.snd f h' = pullback.snd p r ≫ j' ≫ pullback.snd g h' := by
    simpa only [F₂, Category.assoc, correspondenceIncidenceMap_snd, reassoc_of% hj'] using
      reparametrizedIncidenceIso_right U X (G(Y)) T zT w' p r l₂ hl₂ eQ eP hQ hP₂
  have hunit : torusPowerParameterUnit k n u₀ F₁ =
      Units.map (pullback.snd p r).appTop.hom.toMonoidHom aP := by
    rw [← torusPowerParameterUnit_comp k (X := X) (Y := Y) n u₀ j (pullback.snd p r)]
    unfold torusPowerParameterUnit
    have ht : torusSupportCoordinate k (F₁ ≫ pullback.fst f h) =
        torusSupportCoordinate k ((pullback.snd p r ≫ j) ≫ pullback.fst g h) := by
      apply Units.ext
      change ((F₁ ≫ pullback.fst f h) ≫ pullback.snd U.hom (T).hom).appTop
          (multiplicativeGroupBaseChangeCoordinate Sₖ).val =
        (((pullback.snd p r ≫ j) ≫ pullback.fst g h) ≫ pullback.snd X.hom (T).hom).appTop
          (multiplicativeGroupBaseChangeCoordinate Sₖ).val
      rw [Category.assoc, htorus₁]
      simp only [Category.assoc, l₁, gP]
      rfl
    rw [ht, htarget₁]
    simp only [Category.assoc]
    rfl
  have hl₂' : l₂ = (nativeTorusPoint (gP ≫ g) aP).left := by
    change ((j ≫ J₀) ≫ pullback.fst g h') ≫ pullback.snd X.hom (T).hom = _
    rw [torusPowerParameterAmbientGraph_comp k (X := X) (Y := Y) n u₀ j,
      torusPowerCutRetainedParameterGraph_fst]
    change torusPowerCutParameterProjection k (X := X) gP aP ≫ (productSnd X T).left = _
    exact torusPowerCutParameterProjection_snd k (X := X) gP aP
  have hstruct : (F₁ ≫ pullback.fst f h) ≫ f = pullback.snd p r ≫ (gP ≫ g) := by
    calc
      _ = (F₁ ≫ pullback.snd f h) ≫ h := by
        simp only [Category.assoc, pullback.condition («f» := f) («g» := h)]
      _ = _ := by
        rw [htarget₁]
        simp only [Category.assoc, gP, ← pullback.condition («f» := g) («g» := h)]
  have houter : F₁ ≫ J = F₂ := by
    apply torusPowerParameterAmbientGraph_eq_of_projections k (X := U) (Y := Y) n u₀ F₁ F₂
    · exact hbase₂'.trans hbase₁.symm
    · rw [htorus₂, hl₂', hstruct, hunit]
      exact (nativeTorusPoint_comp_left (gP ≫ g) (pullback.snd p r) aP).symm
    · calc
        _ = pullback.snd p r ≫ j ≫ pullback.snd g h := by
          simpa only [Category.assoc, j', torusPowerParameterAmbientGraph_target] using
            congrArg (· ≫ pullback.fst h (T).hom) htarget₂
        _ = _ := htarget₁.symm
    · calc
        _ = pullback.snd p r ≫ l₁ := by
          simpa only [Category.assoc, j', torusPowerParameterAmbientGraph_torus, l₁, gP] using
            congrArg (· ≫ pullback.snd h (T).hom) htarget₂
        _ = _ := htorus₁.symm
  exact reparametrizedIncidenceTorCorrespondence_val_map U X Y (G(Y)) zT w w'
    p r l₁ l₂ hl₁ hl₂ eQ (Iso.refl P) eP hQ hP₁ hP₂ hzT hw hw' J
    ((Category.assoc e₁.hom (correspondenceIncidenceMap f g h zT w) J).symm.trans houter)

end AlgebraicGeometry.Cor

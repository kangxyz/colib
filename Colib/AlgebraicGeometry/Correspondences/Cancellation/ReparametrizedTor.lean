/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedStalkMaps
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedTorusRegular
public import Colib.Algebra.Category.ModuleCat.Tor.RegularBlock
public import Colib.Algebra.Category.ModuleCat.Tor.LocalizedMiddleDiagonal.Length
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.RegularOpenIndependence

/-!
# Native Tor lengths after imposing the free torus equation

The actual Tor of the full parameter incidence has the same degree lengths
as the remaining middle-diagonal Koszul homology on the common coefficient
product. Its remaining equations are taken from the original middle
diagonal and therefore have the same coefficients for both choices of the
right-hand parameter.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

open Scheme.AffineLineFiber

private theorem ker_stalkMapAtImage {A B : Scheme.{u}} (f : A ⟶ B) [IsClosedImmersion f]
    (x : A) (y : B) (hy : y = f x) :
    RingHom.ker (f.stalkMapAtImage x y hy).hom = IdealSheafData.stalk f.ker y := by
  subst y
  rw [Scheme.Hom.stalkMapAtImage_rfl, ker_stalkMap_eq_idealStalk_ker]

private theorem surjective_stalkMapAtImage {A B : Scheme.{u}} (f : A ⟶ B)
    [SurjectiveOnStalks f] (x : A) (y : B) (hy : y = f x) :
    Function.Surjective (f.stalkMapAtImage x y hy).hom := by
  subst y
  rw [Scheme.Hom.stalkMapAtImage_rfl]
  exact SurjectiveOnStalks.stalkMap_surjective f x

private theorem flat_stalkMapAtImage {A B : Scheme.{u}} (f : A ⟶ B) [Flat f]
    (x : A) (y : B) (hy : y = f x) : (f.stalkMapAtImage x y hy).hom.Flat := by
  subst y
  rw [Scheme.Hom.stalkMapAtImage_rfl]
  exact Flat.stalkMap f x

private theorem idealStalk_comap_stalkMapAtImage {A B : Scheme.{u}}
    (I : B.IdealSheafData) (f : A ⟶ B) (x : A) (y : B) (hy : y = f x) :
    IdealSheafData.stalk (I.comap f) x =
      (IdealSheafData.stalk I y).map (f.stalkMapAtImage x y hy).hom := by
  subst y
  rw [Scheme.Hom.stalkMapAtImage_rfl, IdealSheafData.stalk_comap]

private theorem seqComplexTensor_get_map_eq {A B : Type u} [CommRing A] [CommRing B]
    (s : List A) (θ : A →+* B) (N : ModuleCat.{u} B) :
    Koszul.seqComplexTensor (s.map θ).get N =
      Koszul.seqComplexTensor (fun i => θ (s.get i)) N := by
  have aux {m n : ℕ} (hlen : m = n) (f : Fin m → B) (g : Fin n → B) (hfg : HEq f g) :
      Koszul.seqComplexTensor f N = Koszul.seqComplexTensor g N := by
    subst n
    cases hfg
    rfl
  apply aux (List.length_map (as := s) θ)
  apply (Fin.heq_fun_iff (List.length_map (as := s) θ)).mpr
  intro i
  simp only [List.get_eq_getElem, List.getElem_map]

variable {k : Type u} [Field k]

variable (U X Z : SmoothSite (Spec (.of k)))
  (z : pullback (C := Scheme)
    (SmoothSite.product U (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom)
  (w : pullback (C := Scheme)
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product Z (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom)
  {Q P : Scheme.{u}} (p : Q ⟶ X.left) (r : P ⟶ X.left)
  (l : P ⟶ (SmoothSite.multiplicativeGroupObject (Spec (.of k))).left)
  (hl : r ≫ X.hom = l ≫ (SmoothSite.multiplicativeGroupObject (Spec (.of k))).hom)
  (eQ : pullback (C := Scheme) (p ≫ X.hom)
    (SmoothSite.multiplicativeGroupObject (Spec (.of k))).hom ≅ (integralComponentAt z).subscheme)
  (eP : P ≅ (integralComponentAt w).subscheme)
  (hQ : eQ.hom ≫ ((integralComponentAt z).subschemeι ≫ pullback.snd
    (SmoothSite.product U (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom) =
      pullbackParameterExtensionMap p X.hom
        (SmoothSite.multiplicativeGroupObject (Spec (.of k))).hom)
  (hP : eP.hom ≫ ((integralComponentAt w).subschemeι ≫ pullback.fst
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product Z (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom) =
      pullback.lift r l hl)

local notation3 (prettyPrint := false) "T" =>
  SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation3 (prettyPrint := false) "τ" => (T).hom
local notation3 (prettyPrint := false) "ξ" =>
  multiplicativeGroupBaseChangeCoordinate (Spec (.of k))
local notation3 (prettyPrint := false) "f" => (SmoothSite.product U T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Z T).hom

local notation3 (prettyPrint := false) "D" => pullback (p ≫ X.hom) (r ≫ X.hom)
local notation3 (prettyPrint := false) "C" => correspondenceSupportProduct f g h z w
local notation3 (prettyPrint := false) "A" => correspondenceIntersectionAmbient f g h
local notation3 (prettyPrint := false) "B" => exteriorAmbientParameterQuotient U X Z T
local notation3 (prettyPrint := false) "L" => correspondenceTripleProduct f g h
local notation3 (prettyPrint := false) "i" => correspondenceSupportProductInclusion f g h z w
local notation3 (prettyPrint := false) "j" => exteriorAmbientParameterInclusion U X Z T
local notation3 (prettyPrint := false) "j'" => exteriorAmbientRemainingInclusion U X Z T
local notation3 (prettyPrint := false) "a" => exteriorAmbientParameterPair U X Z T
local notation3 (prettyPrint := false) "m" => exteriorAmbientRemainingPair U X Z T
local notation3 (prettyPrint := false) "c" =>
  reparametrizedCoefficientInclusion U X Z T z w p r l hl eQ eP hQ hP
local notation3 (prettyPrint := false) "d" =>
  reparametrizedCoefficientQuotientMap U X Z T z w p r l hl eQ eP hQ hP
local notation3 (prettyPrint := false) "v" => reparametrizedIncidenceToProduct X p r
local notation3 (prettyPrint := false) "m₀" => reparametrizedRemainingMiddlePair X p r

variable (x : pullback («C» := Scheme) p r)

local notation3 (prettyPrint := false) "y" => v x
local notation3 (prettyPrint := false) "xₙ" =>
  reparametrizedStalk_incidencePoint U X Z T z w p r l hl eQ eP hQ hP x
local notation3 (prettyPrint := false) "xₗ" => correspondenceIncidenceInclusion f g h z w xₙ
local notation3 (prettyPrint := false) "xₐ" => i (c y)
local notation3 (prettyPrint := false) "xᵦ" => d y
local notation3 (prettyPrint := false) "xₘ" => m₀ y
local notation3 (prettyPrint := false) "α" =>
  reparametrizedStalk_parameterMap U X Z T z w p r l hl eQ eP hQ hP x
local notation3 (prettyPrint := false) "β" =>
  reparametrizedStalk_remainingMap U X Z T z w p r l hl eQ eP hQ hP x
local notation3 (prettyPrint := false) "σ" =>
  reparametrizedStalk_middleMap U X Z T z w p r l hl eQ eP hQ hP x

set_option maxHeartbeats 600000 in
-- The ordered quotient stalks have distinct coefficient rings and module actions.
/-- Each actual Tor length of the parameter incidence is the length of
the same ordered Koszul homology on the common coefficient product. -/
theorem reparametrizedIncidenceTor_length_eq_remainingKoszul
    (s : List ((pullback X.hom X.hom).presheaf.stalk xₘ))
    (hs : IsRegular ((pullback X.hom X.hom).presheaf.stalk xₘ) s)
    (hk : Ideal.ofList s = IdealSheafData.stalk (pullback.diagonal X.hom).ker xₘ)
    (n : ℕ) :
    Module.length (correspondenceIncidenceAmbientStalk f g h z w xₙ)
      (correspondenceIncidenceAmbientTor f g h z w xₙ n) =
      Module.length ((D).presheaf.stalk y)
        ((Koszul.seqComplexTensor (s.map ((m₀).stalkMap y).hom).get
          (ModuleCat.of ((D).presheaf.stalk y) ((D).presheaf.stalk y))).homology n) := by
  let R : CommRingCat.{u} := (A).presheaf.stalk xₐ
  let C' : CommRingCat.{u} := (C).presheaf.stalk (c y)
  let D' : CommRingCat.{u} := (D).presheaf.stalk y
  let φ : R →+* C' := ((i).stalkMap (c y)).hom
  let ψ : C' →+* D' := ((c).stalkMap y).hom
  let θ : (B).presheaf.stalk xᵦ →+* D' := ((d).stalkMap y).hom
  let t₀ := scalar (torusParameterZeroMap τ ξ 1) 0 (a xₐ)
  let t : R := (a).stalkMap xₐ t₀
  let sB : List ((B).presheaf.stalk xᵦ) := s.map (σ).hom
  let hA := reparametrizedStalk_parameterPoint U X Z T z w p r l hl eQ eP hQ hP x
  let hB := reparametrizedStalk_remainingPoint U X Z T z w p r l hl eQ eP hQ hP x
  let hM := reparametrizedStalk_middlePoint U X Z T z w p r l hl eQ eP hQ hP x
  have hkerα' : RingHom.ker (α).hom = IdealSheafData.stalk (j).ker xₐ :=
    ker_stalkMapAtImage j xᵦ xₐ hA
  let aMap : A ⟶ pullback («C» := Scheme) τ τ := a
  let aPt : pullback («C» := Scheme) τ τ := aMap xₐ
  let A₀ : CommRingCat.{u} := (pullback («C» := Scheme) τ τ).presheaf.stalk aPt
  let a₀ : A₀ →+* R := (aMap.stalkMap xₐ).hom
  have hdiag : IdealSheafData.stalk (pullback.diagonal τ).ker aPt = Ideal.span {t₀} :=
    torusParameterDiagonal_stalk_ideal aPt
  have hkerα : RingHom.ker (α).hom = Ideal.ofList [t] := by
    rw [hkerα', exteriorAmbientParameterInclusion_ker, IdealSheafData.stalk_comap]
    change Ideal.map a₀ (IdealSheafData.stalk (pullback.diagonal τ).ker aPt) =
      Ideal.ofList [a₀ t₀]
    rw [hdiag, Ideal.map_span, Set.image_singleton, Ideal.ofList_singleton]
  have ht : IsSMulRegular R t := by
    let : Algebra A₀ R := a₀.toAlgebra
    let : Module.Flat A₀ R := Flat.stalkMap aMap xₐ
    change IsSMulRegular R (algebraMap A₀ R t₀)
    exact IsSMulRegular.of_flat (R := A₀) (S := R)
      (torusParameterZeroMap_scalar_regular τ ξ aPt)
  have hregα : IsRegular R [t] := by
    refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ (fun u hu => ?_)
      ((isWeaklyRegular_singleton_iff R t).mpr ht)
    apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (α).hom)
    rw [hkerα]
    exact Ideal.subset_span hu
  have hcSq := reparametrizedCoefficientQuotientMap_isPullback U X Z T z w
    p r l hl eQ eP hQ hP
  let : IsClosedImmersion c :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hcSq inferInstance
  have hcKer : (c).ker = (j).ker.comap i := by
    rw [← hcSq.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hkerψ : RingHom.ker ψ = Ideal.ofList ([t].map φ) := by
    change RingHom.ker ((c).stalkMap y).hom = _
    rw [ker_stalkMap_eq_idealStalk_ker, hcKer, IdealSheafData.stalk_comap,
      ← hkerα', hkerα, Ideal.map_ofList]
  have hregψ : IsWeaklyRegular C' ([t].map φ) := by
    rw [List.map_singleton, isWeaklyRegular_singleton_iff]
    have hRegular := reparametrized_torusScalar_regular U X Z z w p r l hl eQ eP hQ hP (c y)
    let i₀ : C ⟶ A := i
    let s₀ : A₀ := t₀
    have he : (i₀ ≫ aMap).stalkMap (c y) s₀ = φ t :=
      ConcreteCategory.congr_hom (Scheme.Hom.stalkMap_comp i₀ aMap (c y)) s₀
    change IsSMulRegular C' ((i₀ ≫ aMap).stalkMap (c y) s₀) at hRegular
    exact he ▸ hRegular
  have hkerβ : RingHom.ker (β).hom = Ideal.ofList sB := by
    rw [reparametrizedStalk_remainingMap, ker_stalkMapAtImage,
      exteriorAmbientRemainingInclusion_ker,
      idealStalk_comap_stalkMapAtImage _ m xᵦ xₘ hM, ← hk, Ideal.map_ofList]
    rfl
  have hregβ : IsRegular ((B).presheaf.stalk xᵦ) sB := by
    refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ (fun u hu => ?_) ?_
    · apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (β).hom)
      rw [hkerβ]
      exact Ideal.subset_span hu
    · exact Stacks.AlgebraicGeometry.isWeaklyRegular_map_of_flat (σ).hom
        (flat_stalkMapAtImage m xᵦ xₘ hM) hs.toIsWeaklyRegular
  have hsq : ψ.comp φ = θ.comp (α).hom := congrArg CommRingCat.Hom.hom
    (reparametrizedStalk_parameterSquare U X Z T z w p r l hl eQ eP hQ hP x)
  have hα : Function.Surjective (α).hom := surjective_stalkMapAtImage j xᵦ xₐ hA
  have hβ : Function.Surjective (β).hom := surjective_stalkMapAtImage j' xₗ xᵦ hB
  have hψ : Function.Surjective ψ := SurjectiveOnStalks.stalkMap_surjective c y
  let eBlock := ModuleCat.Tor.regularLeadingBlockIso (α).hom (β).hom φ ψ θ hsq hα hβ hψ
    [t] sB hregα hkerα hregψ hkerψ hregβ hkerβ n
  have hlist : sB.map θ = s.map ((m₀).stalkMap y).hom := by
    change (s.map (σ).hom).map θ = _
    rw [List.map_map]
    exact congrArg (fun F => s.map F) (funext fun x' =>
      ConcreteCategory.congr_hom
        (reparametrizedStalk_middleCoefficient U X Z T z w p r l hl eQ eP hQ hP x) x')
  let N := ModuleCat.of D' D'
  let K := Koszul.seqComplexTensor (s.map ((m₀).stalkMap y).hom).get N
  let eK :
      (Koszul.seqComplexTensor (fun index => θ (sB.get index)) N).homology n ≅ K.homology n :=
    eqToIso (congrArg (fun H => H.homology n) ((seqComplexTensor_get_map_eq sB θ N).symm.trans
      (congrArg (fun L' : List D' => Koszul.seqComplexTensor L'.get N) hlist)))
  let hC := reparametrizedStalk_supportPoint U X Z T z w p r l hl eQ eP hQ hP x
  let eR := correspondenceIncidenceAmbientStalkIsoOfSupportPoint f g h z w xₙ (c y) hC
  let eNative := correspondenceIncidenceAmbientTorIsoOfSupportPoint f g h z w xₙ (c y) hC
    ((β).hom.comp (α).hom)
    (congrArg CommRingCat.Hom.hom
      (reparametrizedStalk_tripleMap U X Z T z w p r l hl eQ eP hQ hP x)) n
  let κ := (ψ.comp φ).comp eR.hom.hom
  let eFinal := eNative ≪≫ (ModuleCat.restrictScalars eR.hom.hom).mapIso
    (eBlock ≪≫ (ModuleCat.restrictScalars (ψ.comp φ)).mapIso eK) ≪≫
    (ModuleCat.restrictScalarsComp'App eR.hom.hom (ψ.comp φ) κ rfl (K.homology n)).symm
  have hκ : Function.Surjective κ := hψ.comp
    ((SurjectiveOnStalks.stalkMap_surjective i (c y)).comp
      (ConcreteCategory.bijective_of_isIso eR.hom).2)
  exact eFinal.toLinearEquiv.length_eq.trans
    (ModuleCat.length_restrictScalars_of_surjective κ hκ (K.homology n))

end Stacks.Chow

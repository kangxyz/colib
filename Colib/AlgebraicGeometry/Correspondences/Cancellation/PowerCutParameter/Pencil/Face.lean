/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil.FaceSupport
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PrincipalCutFaceGeometry
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor
import Colib.AlgebraicGeometry.Chow.IntegralFundamental
import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedPrimeSupports
import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Parameters

/-!
# Cycle specialization for the Laurent pencil

For a nonzero section with finite, generically dominant cut, precomposition
by a scalar graph gives the entire zero cut of the restricted section.
The comparison uses the original closed support and the full endpoint
stalk lengths.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction AffineLineFiber
open AlgebraicCycle

private theorem polynomialEndpointMap_fundamentalCycle_integral {k : Type u} [Field k]
    {D : Scheme.{u}} [IsIntegral D] [IsNoetherian D]
    (f : D ⟶ Spec (.of (Polynomial k))) (a : k) :
    letI : IsNoetherian (fiber f a) := isNoetherian_of_finiteType (inclusion f a)
    polynomialEndpointMap f a (fundamentalCycle D) = fundamentalCycle (fiber f a) := by
  classical
  let : IsNoetherian (fiber f a) := isNoetherian_of_finiteType (inclusion f a)
  let i := (integralComponentAt (genericPoint D)).subschemeι
  let : IsIso i := isIso_integralComponentAt_genericPoint_inclusion
  let : IsNoetherian (fiber (i ≫ f) a) :=
    isNoetherian_of_finiteType (inclusion (i ≫ f) a ≫ i)
  let : IsIso (AffineLineFiber.fiberMap f a i) :=
    MorphismProperty.of_isPullback (AffineLineFiber.fiberMap_isPullback f a i).flip inferInstance
  rw [fundamentalCycle_eq_single_genericPoint, polynomialEndpointMap_single, one_zsmul]
  exact finiteCyclePushforward_fundamentalCycle_iso (asIso (AffineLineFiber.fiberMap f a i))

private theorem sectionCutSupportMap_eq_comp {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {D : Scheme.{u}}
    (m : D ⟶ pullback X.hom Y.hom) (p : D ⟶ X.left) (q : D ⟶ Y.left)
    (hp : m ≫ pullback.fst X.hom Y.hom = p) (hq : m ≫ pullback.snd X.hom Y.hom = q)
    (h : p ≫ X.hom = q ≫ Y.hom) (s : Γ(D, ⊤)) :
    sectionCutSupportMap (X := X) (Y := Y) (P := D) p q h s =
      inclusion (sectionToAffineLine (p ≫ X.hom) s) 0 ≫ m := by
  let i := inclusion (sectionToAffineLine (p ≫ X.hom) s) 0
  apply pullback.hom_ext
  · exact (sectionCutSupportMap_fst p q h s).trans
      ((congrArg (i ≫ ·) hp.symm).trans (Category.assoc _ _ _).symm)
  · exact (sectionCutSupportMap_snd p q h s).trans
      ((congrArg (i ≫ ·) hq.symm).trans (Category.assoc _ _ _).symm)

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
  (j : P ⟶ pullback
    (product X (multiplicativeGroupObject (Spec (.of k)))).hom
    (product Y (multiplicativeGroupObject (Spec (.of k)))).hom)

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "A₁" => additiveGroupObject Sₖ
local notation "XG" => (product X T)
local notation "YG" => (product Y T)
local notation "V" => (torusPowerCutRetainedTarget k Y)
local notation "B" => (product X A₁)
set_option quotPrecheck false in
local notation "g" => (j ≫ pullback.fst (XG).hom (YG).hom)
set_option quotPrecheck false in
local notation "r" => (j ≫ (torusPowerCutAmbientSchemeIso k X Y).hom)
set_option quotPrecheck false in
local notation "b" => (g ≫ (XG).hom)
set_option quotPrecheck false in
local notation "W" => pullback (C := Scheme) b (A₁).hom
set_option quotPrecheck false in
local notation "π" => pullback.fst b (A₁).hom
local notation "p" => torusPowerCutPencilProjection k g
local notation "p₀" => torusSupportBaseProjection k g
local notation "m" => torusPowerCutPencilRetainedSupportMap k j
set_option quotPrecheck false in
local notation "v" => (m ≫ pullback.snd (B).hom (V).hom)
set_option quotPrecheck false in
local notation "v₀" => (r ≫ pullback.snd X.hom (V).hom)
local notation "q" => nativeAdditivePolynomialParameter X.hom
local notation "f" => nativeAdditivePolynomialParameter b
local notation "σ(" a ")" => nativeAdditiveParameterSection b a
local notation "φ(" a ")" => nativeAffineSection (CommRingCat.of k) X a
set_option quotPrecheck false in
local notation "sMap(" s ")" => sectionToAffineLine (p ≫ (B).hom) s
set_option quotPrecheck false in
local notation "sMap₀(" a ", " s ")" => sectionToAffineLine (p₀ ≫ X.hom) ((σ(a)).appTop s)

/-- The two actual projections of the retained pencil support agree over the coefficient field. -/
theorem torusPowerCutPencilRetainedSupport_over :
    p ≫ (B).hom = v ≫ (V).hom := by
  have hp := congrArg (· ≫ (B).hom) (torusPowerCutPencilRetainedSupportMap_fst k j).symm
  have he := congrArg (m ≫ ·) (pullback.condition («f» := (B).hom) («g» := (V).hom))
  exact hp.trans ((Category.assoc _ _ _).trans (he.trans (Category.assoc _ _ _).symm))

/-- The retained endpoint projections agree over the coefficient field. -/
theorem torusPowerCutPencilRetainedEndpoint_over :
    p₀ ≫ X.hom = v₀ ≫ (V).hom := by
  have hp := congrArg (· ≫ X.hom) (torusPowerCutPencilRetainedEndpoint_fst k j).symm
  have he := congrArg (r ≫ ·) (pullback.condition («f» := X.hom) («g» := (V).hom))
  exact hp.trans ((Category.assoc _ _ _).trans (he.trans (Category.assoc _ _ _).symm))

set_option maxHeartbeats 1600000 in
-- The endpoint comparison elaborates nested native pullbacks and finite pushforwards.
/-- A principal pencil cut specializes with the entire cycle of the restricted section. -/
theorem graph_comp_torusPowerCutPencilSectionCut [IsIntegral P] [IsNoetherian P]
    [IsClosedImmersion j] (a : k) (s : Γ(W, ⊤)) (hs : s ≠ 0)
    [IsFinite (inclusion (sMap(s)) 0 ≫ p)]
    [IsFinite (inclusion (sMap₀(a, s)) 0 ≫ p₀)]
    (hgen : ∀ x : genericPoints (fiber (sMap(s)) 0),
      (inclusion (sMap(s)) 0 ≫ p) x.val ∈ genericPoints (B).left)
    (hgen₀ : ∀ x : genericPoints (fiber (sMap₀(a, s)) 0),
      (inclusion (sMap₀(a, s)) 0 ≫ p₀) x.val ∈ genericPoints X.left) :
    (graphFunctor k).map (φ(a)) ≫
      sectionCutCorrespondence (X := B) (Y := V) (P := W)
        p v (torusPowerCutPencilRetainedSupport_over k j) s hgen =
    sectionCutCorrespondence (X := X) (Y := V) (P := P)
      p₀ v₀ (torusPowerCutPencilRetainedEndpoint_over k j)
      ((σ(a)).appTop s) hgen₀ := by
  let : IsIntegral W := inferInstanceAs (IsIntegral (pullback b (A₁).hom))
  let : IsNoetherian W := isNoetherian_of_finiteType π
  let : IsNoetherian (fiber (sMap(s)) 0) := isNoetherian_of_finiteType (inclusion (sMap(s)) 0)
  let : IsNoetherian (fiber (sMap₀(a, s)) 0) :=
    isNoetherian_of_finiteType (inclusion (sMap₀(a, s)) 0)
  let : IsFinite (inclusion (sMap(s)) 0 ≫ (m ≫ pullback.fst (B).hom (V).hom)) := by
    rw [torusPowerCutPencilRetainedSupportMap_fst]
    infer_instance
  have hg (x : W) : IsSMulRegular ((W).presheaf.stalk x) (scalar (sMap(s)) 0 x) := by
    rw [sectionToAffineLine_zero_scalar]
    exact IsSMulRegular.of_ne_zero
      ((map_ne_zero_iff _ (germ_injective_of_isIntegral W x (Opens.mem_top _))).mpr hs)
  let α : Cor.mk B ⟶ Cor.mk V :=
    sectionCutCorrespondence (X := B) (Y := V) (P := W)
      p v (torusPowerCutPencilRetainedSupport_over k j) s hgen
  let β : Cor.mk X ⟶ Cor.mk V :=
    sectionCutCorrespondence (X := X) (Y := V) (P := P)
      p₀ v₀ (torusPowerCutPencilRetainedEndpoint_over k j) ((σ(a)).appTop s) hgen₀
  let i := inclusion (sMap(s)) 0
  let αm := sectionCutSupportMap (X := B) (Y := V) (P := W)
    p v (torusPowerCutPencilRetainedSupport_over k j) s
  have hαm : αm = i ≫ m :=
    sectionCutSupportMap_eq_comp (X := B) (Y := V) m p v
      (torusPowerCutPencilRetainedSupportMap_fst k j) rfl
      (torusPowerCutPencilRetainedSupport_over k j) s
  have hα : α.val = finiteCyclePushforward m (finiteCyclePushforward i (fundamentalCycle
      (fiber (sMap(s)) 0))) := by
    calc
      _ = finiteCyclePushforward αm (fundamentalCycle (fiber (sMap(s)) 0)) :=
        sectionCutCorrespondence_val (X := B) (Y := V) (P := W)
          p v (torusPowerCutPencilRetainedSupport_over k j) s hgen
      _ = finiteCyclePushforward (i ≫ m) (fundamentalCycle (fiber (sMap(s)) 0)) :=
        DFunLike.congr_fun (AlgebraicCycle.finiteCyclePushforward_congr _ _ hαm) _
      _ = _ := (finiteCyclePushforward_comp_apply i m _).symm
  let e := nativeAdditiveParameterFiberIso b a
  let F := fiber f a
  let h := inclusion f a ≫ sMap(s)
  let c := closedSupportEndpointMapOfParameterEq (φ(a)) q a
    (torusPowerCutPencilFace_isPullback k X a) m f
    (torusPowerCutPencilRetainedSupport_parameter k j)
  let : IsIntegral F := IsIntegral.of_isIso e.hom
  let : IsNoetherian F := isNoetherian_of_finiteType e.inv
  let : IsNoetherian (fiber h 0) := isNoetherian_of_finiteType (inclusion h 0)
  have heq : sMap₀(a, s) = e.hom ≫ h := by
    let iₐ : P ⟶ W := σ(a)
    have hi : iₐ ≫ π = 𝟙 P := nativeAdditiveParameterSection_fst b a
    have hb : iₐ ≫ p ≫ (B).hom = p₀ ≫ X.hom := by
      calc
        _ = iₐ ≫ π ≫ b := congrArg (iₐ ≫ ·) (torusPowerCutPencilProjection_over k g)
        _ = (iₐ ≫ π) ≫ b := (Category.assoc _ _ _).symm
        _ = b := (congrArg (· ≫ b) hi).trans (Category.id_comp _)
        _ = _ := (Category.assoc _ _ _).symm
    have he : e.hom ≫ inclusion f a = iₐ := nativeAdditiveParameterFiberIso_hom_inclusion b a
    calc
      _ = sectionToAffineLine (iₐ ≫ p ≫ (B).hom) (iₐ.appTop s) :=
        congrArg (fun u : P ⟶ Sₖ => sectionToAffineLine u (iₐ.appTop s)) hb.symm
      _ = iₐ ≫ sMap(s) := sectionToAffineLine_comp iₐ (p ≫ (B).hom) s
      _ = (e.hom ≫ inclusion f a) ≫ sMap(s) := congrArg (· ≫ sMap(s)) he.symm
      _ = _ := Category.assoc _ _ _
  let e₁ := pullback.congrHom (rfl : point (0 : k) = point 0) heq
  let : IsIso (AffineLineFiber.fiberMap h 0 e.hom) :=
    MorphismProperty.of_isPullback
      (AffineLineFiber.fiberMap_isPullback h 0 e.hom).flip inferInstance
  let e₀ := e₁ ≪≫ asIso (AffineLineFiber.fiberMap h 0 e.hom)
  let i₀ := inclusion (sMap₀(a, s)) 0
  have he₁ : e₁.hom ≫ inclusion (e.hom ≫ h) 0 = i₀ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have he₀ : e₀.hom ≫ inclusion h 0 = inclusion (sMap₀(a, s)) 0 ≫ e.hom := by
    calc
      _ = e₁.hom ≫ AffineLineFiber.fiberMap h 0 e.hom ≫ inclusion h 0 :=
        Category.assoc _ _ _
      _ = e₁.hom ≫ inclusion (e.hom ≫ h) 0 ≫ e.hom :=
        congrArg (e₁.hom ≫ ·) (AffineLineFiber.fiberMap_inclusion h 0 e.hom)
      _ = (e₁.hom ≫ inclusion (e.hom ≫ h) 0) ≫ e.hom := (Category.assoc _ _ _).symm
      _ = _ := congrArg (· ≫ e.hom) he₁
  have hc : e.hom ≫ c = r := torusPowerCutPencilRetainedSupportMap_endpoint k j a
  let βm := sectionCutSupportMap (X := X) (Y := V) (P := P)
    p₀ v₀ (torusPowerCutPencilRetainedEndpoint_over k j) ((σ(a)).appTop s)
  have hβm : βm = i₀ ≫ r :=
    sectionCutSupportMap_eq_comp (X := X) (Y := V) r p₀ v₀
      (torusPowerCutPencilRetainedEndpoint_fst k j) rfl
      (torusPowerCutPencilRetainedEndpoint_over k j) ((σ(a)).appTop s)
  have hm : (e₀.hom ≫ inclusion h 0) ≫ c = βm := by
    calc
      _ = (i₀ ≫ e.hom) ≫ c := congrArg (· ≫ c) he₀
      _ = i₀ ≫ e.hom ≫ c := Category.assoc _ _ _
      _ = i₀ ≫ r := congrArg (i₀ ≫ ·) hc
      _ = _ := hβm.symm
  have hβ : β.val = finiteCyclePushforward c (finiteCyclePushforward (inclusion h 0)
      (polynomialEndpointMap h 0 (fundamentalCycle F))) := by
    let d := fundamentalCycle (fiber (sMap₀(a, s)) 0)
    have hd : finiteCyclePushforward e₀.hom d = polynomialEndpointMap h 0 (fundamentalCycle F) :=
      (finiteCyclePushforward_fundamentalCycle_iso e₀).trans
        (polynomialEndpointMap_fundamentalCycle_integral h 0).symm
    calc
      _ = finiteCyclePushforward βm d :=
        sectionCutCorrespondence_val (X := X) (Y := V) (P := P)
          p₀ v₀ (torusPowerCutPencilRetainedEndpoint_over k j) ((σ(a)).appTop s) hgen₀
      _ = finiteCyclePushforward ((e₀.hom ≫ inclusion h 0) ≫ c) d :=
        DFunLike.congr_fun (AlgebraicCycle.finiteCyclePushforward_congr _ _ hm.symm) d
      _ = finiteCyclePushforward c (finiteCyclePushforward (e₀.hom ≫ inclusion h 0) d) :=
        (finiteCyclePushforward_comp_apply (e₀.hom ≫ inclusion h 0) c d).symm
      _ = finiteCyclePushforward c (finiteCyclePushforward (inclusion h 0)
          (finiteCyclePushforward e₀.hom d)) :=
        congrArg (finiteCyclePushforward c)
          (finiteCyclePushforward_comp_apply e₀.hom (inclusion h 0) d).symm
      _ = _ := congrArg
        (fun d => finiteCyclePushforward c (finiteCyclePushforward (inclusion h 0) d)) hd
  have hgen' (x : genericPoints (fiber (sMap(s)) 0)) :
      (m ≫ pullback.fst (B).hom (V).hom) (i x.val) ∈ genericPoints (B).left := by
    rw [torusPowerCutPencilRetainedSupportMap_fst]
    exact hgen x
  exact graph_comp_closedFiberCycle_endpoint_eq_of_finite (Y := B) (Z := V) (P := W) (φ(a)) q a
    (torusPowerCutPencilFace_isPullback k X a) m f
    (torusPowerCutPencilRetainedSupport_parameter k j) (sMap(s)) 0 hgen'
    (scalar_regular f a) hg α hα β hβ

end AlgebraicGeometry.Cor

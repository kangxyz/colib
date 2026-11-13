/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.UnitEndpoint
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.UnitFiber
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.UnitSection
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.AmbientGraph
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedPrimeSupports
import Colib.AlgebraicGeometry.Correspondences.Graph.EndpointSingleFiber
import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward

/-!
# A reparametrized prime cut is actual unit graph precomposition

Taking the unit fibre of the retained power graph gives the original
whole section zero scheme. Its finite pushforward followed by the
target projection is the original principal cut correspondence.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction AffineLineFiber
open AlgebraicCycle

private theorem graph_comp_prime_val_eq_fiber_pushforward {k : Type u} [Field k]
    {X U V : SmoothSite (Spec (.of k))} {D : Scheme.{u}} [IsNoetherian D]
    (φ : X ⟶ U) (q : U.left ⟶ Spec (.of (Polynomial k))) [Flat q] (a : k)
    (H : IsPullback φ.left X.hom q (point a))
    (z : pullback (C := Scheme) U.hom V.hom)
    (hz : IsFiniteCorrespondencePoint U.hom V.hom z)
    (e : D ≅ correspondenceGraphFiber U.hom V.hom z φ.left)
    (m : D ⟶ pullback X.hom V.hom) [IsFinite m]
    (hm : e.hom ≫ correspondenceGraphFiberMap X.hom U.hom V.hom z φ.left
      (MorphismProperty.Over.w φ) = m) :
    ((graphFunctor k).map φ ≫ singleFiniteCorrespondence U.hom V.hom z hz 1).val =
      finiteCyclePushforward m (fundamentalCycle D) := by
  let F := correspondenceGraphFiberMap X.hom U.hom V.hom z φ.left (MorphismProperty.Over.w φ)
  let : IsFinite F := isFinite_correspondenceGraphFiberMap X.hom U.hom V.hom z φ.left
    (MorphismProperty.Over.w φ) hz
  let : IsNoetherian (correspondenceGraphFiber U.hom V.hom z φ.left) :=
    isNoetherian_correspondenceGraphFiber U.hom V.hom z φ.left hz
  calc
    _ = finiteCyclePushforward F
        (fundamentalCycle (correspondenceGraphFiber U.hom V.hom z φ.left)) :=
      graph_comp_single_val_eq_fiber_of_cartesian_endpoint φ q a H z hz
    _ = finiteCyclePushforward F (finiteCyclePushforward e.hom (fundamentalCycle D)) :=
      congrArg (finiteCyclePushforward F) (finiteCyclePushforward_fundamentalCycle_iso e).symm
    _ = finiteCyclePushforward (e.hom ≫ F) (fundamentalCycle D) :=
      finiteCyclePushforward_comp_apply e.hom F _
    _ = _ := DFunLike.congr_fun (AlgebraicCycle.finiteCyclePushforward_congr _ _ hm) _

variable (k : Type u) [Field k] (X Y : SmoothSite (Spec (.of k)))

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "G(" X ")" => product X T
local notation "V(" Y ")" => torusPowerCutRetainedTarget k Y

/-- Forget both retained torus coordinates. -/
def torusPowerParameterForget : V(Y) ⟶ Y := productFst (G(Y)) T ≫ productFst Y T

set_option quotPrecheck false in
local notation "g" => (G(X)).hom
set_option quotPrecheck false in
local notation "h" => (G(Y)).hom
set_option quotPrecheck false in
local notation "h'" => (V(Y)).hom
local notation "A" => pullback (C := Scheme) g h
set_option quotPrecheck false in
local notation "P(" w ")" => (integralComponentAt (X := A) w).subscheme
set_option quotPrecheck false in
local notation "j(" w ")" => (integralComponentAt (X := A) w).subschemeι
set_option quotPrecheck false in
local notation "p(" w ")" => torusSupportBaseProjection k (X := X) (j(w) ≫ pullback.fst g h)
set_option quotPrecheck false in
local notation "q(" w ")" => torusSupportBaseProjection k (X := Y) (j(w) ≫ pullback.snd g h)
set_option quotPrecheck false in
local notation "F(" w ", " n ", " u₀ ")" =>
  sectionToAffineLine (p(w) ≫ X.hom) (torusPowerParameterSection k X Y w n u₀)

set_option maxHeartbeats 600000 in
-- The actual graph fibre and its full closed support require nested pullback elaboration.
private theorem torusPowerParameterUnitPrime_cut_aux
    (w : A) (n : ℕ) (u₀ : (Γ((G(Y)).left, ⊤))ˣ)
    (hw' : IsFiniteCorrespondencePoint g h' (torusPowerParameterAmbientGraph k (X := X) n u₀ w))
    [IsFinite (AffineLineFiber.inclusion (F(w, n, u₀)) 0 ≫ p(w))]
    (hgen : ∀ a : genericPoints (fiber (F(w, n, u₀)) 0),
      (AffineLineFiber.inclusion (F(w, n, u₀)) 0 ≫ p(w)) a.val ∈ genericPoints X.left) :
    ((graphFunctor k).map (unitSection.app X) ≫
        (singleFiniteCorrespondence g h' _ hw' 1 : Cor.mk (G(X)) ⟶ Cor.mk (V(Y)))) ≫
      (graphFunctor k).map (torusPowerParameterForget k Y) =
      torusPowerParameterSectionCut k X Y w n u₀ hgen := by
  let P := P(w)
  let j : P ⟶ A := j(w)
  let p : P ⟶ X.left := p(w)
  let q : P ⟶ Y.left := q(w)
  let J := torusPowerParameterAmbientGraph k (X := X) n u₀
  let w' := J w
  let s := torusPowerParameterSection k X Y w n u₀
  let Z := fiber (F(w, n, u₀)) 0
  let i : Z ⟶ P := AffineLineFiber.inclusion (F(w, n, u₀)) 0
  let : IsNoetherian (pullback (C := Scheme) g h) :=
    SmoothSite.isNoetherian_overField k (product (G(X)) (G(Y)))
  let : IsNoetherian P := Scheme.isNoetherian_of_finiteType_of_isNoetherian j
  let : IsNoetherian X.left := SmoothSite.isNoetherian_overField k X
  let : IsClosedImmersion i := inferInstanceAs
    (IsClosedImmersion (AffineLineFiber.inclusion (F(w, n, u₀)) 0))
  let : IsNoetherian Z := Scheme.isNoetherian_of_finiteType_of_isNoetherian i
  let : IsIntegral P := isIntegral_integralComponentAt w
  let gP := j ≫ pullback.fst g h
  let j' := j ≫ J
  let aP := torusPowerParameterUnit k n u₀ j
  let qV := j' ≫ pullback.snd g h'
  let φ := unitSection.app X
  have hη : j' (genericPoint P) = w' := congrArg J (genericPointOf_integralComponentAt w)
  let eP := closedIntegralSupportIsoOfEq j' w' hη
  have heP : eP.hom ≫ (integralComponentAt w').subschemeι = j' :=
    closedIntegralSupportIsoOfEq_hom_inclusion j' w' hη
  have hj' : j' = torusPowerCutRetainedParameterGraph k j aP :=
    torusPowerParameterAmbientGraph_comp k n u₀ j
  have hsrc : j' ≫ pullback.fst g h' = torusPowerCutParameterProjection k gP aP := by
    rw [hj', torusPowerCutRetainedParameterGraph_fst]
  have hq : p ≫ X.hom = qV ≫ (V(Y)).hom := by
    have hp : torusPowerCutParameterProjection k gP aP ≫ (productFst X T).left = p :=
      torusPowerCutParameterProjection_fst k gP aP
    calc
      _ = (torusPowerCutParameterProjection k gP aP ≫ (productFst X T).left) ≫ X.hom :=
        congrArg (· ≫ X.hom) hp.symm
      _ = torusPowerCutParameterProjection k gP aP ≫ g := Category.assoc _ _ _
      _ = (j' ≫ pullback.fst g h') ≫ g := congrArg (· ≫ g) hsrc.symm
      _ = _ := by simp only [qV, Category.assoc, pullback.condition]
  have hZ : IsPullback i (i ≫ p) (torusPowerCutParameterProjection k gP aP) φ.left :=
    isPullback_torusPowerCutParameterProjection_unitSection k gP
      ((torusSupportCoordinate k gP) ^ n)
      (Units.map ((j ≫ pullback.snd g h).appTop.hom.toMonoidHom) u₀)
  have heParameter : eP.hom ≫ ((integralComponentAt w').subschemeι ≫ pullback.fst g h') =
      torusPowerCutParameterProjection k gP aP := by
    rw [← Category.assoc, heP, hsrc]
  have hfibre : IsPullback (i ≫ p) (i ≫ eP.hom) φ.left
      ((integralComponentAt w').subschemeι ≫ pullback.fst g h') :=
    hZ.flip.of_iso (Iso.refl _) (Iso.refl _) eP (Iso.refl _)
      (by simp) (by simp) (by simp)
      (by simpa only [Iso.refl_hom, Category.comp_id] using heParameter.symm)
  let eZ := hfibre.isoPullback
  let F := correspondenceGraphFiberMap X.hom g h' w' φ.left (MorphismProperty.Over.w φ)
  let m := sectionCutSupportMap (X := X) (Y := V(Y)) («P» := P) p qV hq s
  have hm : eZ.hom ≫ F = m := by
    apply pullback.hom_ext
    · have he := hfibre.isoPullback_hom_fst
      calc
        _ = eZ.hom ≫ (F ≫ pullback.fst X.hom h') := Category.assoc _ _ _
        _ = eZ.hom ≫ pullback.fst φ.left
            ((integralComponentAt w').subschemeι ≫ pullback.fst g h') :=
          congrArg (eZ.hom ≫ ·) (correspondenceGraphFiberMap_fst X.hom g h' w' φ.left _)
        _ = i ≫ p := he
        _ = _ := (sectionCutSupportMap_fst (X := X) (Y := V(Y)) p qV hq s).symm
    · let l := (integralComponentAt w').subschemeι ≫ pullback.snd g h'
      let π := pullback.snd φ.left ((integralComponentAt w').subschemeι ≫ pullback.fst g h')
      have he : eZ.hom ≫ π = i ≫ eP.hom := hfibre.isoPullback_hom_snd
      have hl : eP.hom ≫ l = qV :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.snd g h') heP)
      calc
        _ = eZ.hom ≫ (F ≫ pullback.snd X.hom h') := Category.assoc _ _ _
        _ = eZ.hom ≫ π ≫ l :=
          congrArg (eZ.hom ≫ ·) (correspondenceGraphFiberMap_snd X.hom g h' w' φ.left _)
        _ = (eZ.hom ≫ π) ≫ l := (Category.assoc _ _ _).symm
        _ = (i ≫ eP.hom) ≫ l := congrArg (· ≫ l) he
        _ = i ≫ qV := (Category.assoc _ _ _).trans (congrArg (i ≫ ·) hl)
        _ = _ := (sectionCutSupportMap_snd (X := X) (Y := V(Y)) p qV hq s).symm
  let γ : Cor.mk (G(X)) ⟶ Cor.mk (V(Y)) := singleFiniteCorrespondence g h' w' hw' 1
  let β : Cor.mk X ⟶ Cor.mk (V(Y)) :=
    sectionCutCorrespondence (X := X) (Y := V(Y)) («P» := P) p qV hq s hgen
  have hret : (graphFunctor k).map φ ≫ γ = β := by
    apply Subtype.ext
    have hβ : β.val = finiteCyclePushforward m (fundamentalCycle Z) :=
      sectionCutCorrespondence_val (X := X) (Y := V(Y)) («P» := P) p qV hq s hgen
    exact (graph_comp_prime_val_eq_fiber_pushforward φ (torusPowerSourceAffineLine k X) 1
      (torusUnitSection_affineLine_isPullback k X) w' hw' eZ m hm).trans hβ.symm
  have hforget : qV ≫ (torusPowerParameterForget k Y).left = q := by
    let π := pullback.snd g h'
    let r := pullback.fst h (T).hom
    let t := (productFst Y T).left
    have ht : J ≫ π ≫ r = pullback.snd g h := torusPowerParameterAmbientGraph_target k n u₀
    change ((j ≫ J) ≫ π) ≫ r ≫ t = (j ≫ pullback.snd g h) ≫ t
    calc
      _ = (j ≫ (J ≫ π ≫ r)) ≫ t := by simp only [Category.assoc]
      _ = _ := congrArg (fun l => (j ≫ l) ≫ t) ht
  change ((graphFunctor k).map φ ≫ γ) ≫ (graphFunctor k).map (torusPowerParameterForget k Y) = _
  rw [hret]
  dsimp only [β]
  rw [sectionCutCorrespondence_comp_graph]
  have hcongr {q₁ q₂ : P ⟶ Y.left} (he : q₁ = q₂)
      (h₁ : p ≫ X.hom = q₁ ≫ Y.hom) (h₂ : p ≫ X.hom = q₂ ≫ Y.hom) :
      sectionCutCorrespondence (X := X) (Y := Y) («P» := P) p q₁ h₁ s hgen =
        sectionCutCorrespondence (X := X) (Y := Y) («P» := P) p q₂ h₂ s hgen := by
    subst q₂
    rfl
  exact (hcongr hforget _ _).trans
    (show _ = torusPowerParameterSectionCut k X Y w n u₀ hgen from rfl)

/-- Precomposition by the unit graph followed by forgetting the retained
coordinates gives the whole original section cut. -/
theorem torusPowerParameterUnitPrime_cut
    (w : A) (n : ℕ) (u₀ : (Γ((G(Y)).left, ⊤))ˣ)
    (hw' : IsFiniteCorrespondencePoint g h' (torusPowerParameterAmbientGraph k (X := X) n u₀ w))
    [IsFinite (AffineLineFiber.inclusion (F(w, n, u₀)) 0 ≫ p(w))]
    (hgen : ∀ a : genericPoints (fiber (F(w, n, u₀)) 0),
      (AffineLineFiber.inclusion (F(w, n, u₀)) 0 ≫ p(w)) a.val ∈ genericPoints X.left) :
    (graphFunctor k).map (unitSection.app X) ≫
        (singleFiniteCorrespondence g h' _ hw' 1 : Cor.mk (G(X)) ⟶ Cor.mk (V(Y))) ≫
          (graphFunctor k).map (torusPowerParameterForget k Y) =
      torusPowerParameterSectionCut k X Y w n u₀ hgen := by
  rw [← Category.assoc]
  exact torusPowerParameterUnitPrime_cut_aux k X Y w n u₀ hw' hgen

end AlgebraicGeometry.Cor

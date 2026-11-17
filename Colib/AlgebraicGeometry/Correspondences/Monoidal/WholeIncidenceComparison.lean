/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.FiniteExteriorPushforward
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.KoszulDevissage
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ProductIdeal
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ProductTorCoefficient

/-!
# The whole product support and the product of middle diagonals

The permutation on the correspondence ambients identifies the two native
Cartesian intersections before passing to any stalk. Its restrictions
are the actual maps of the full support schemes and of the diagonals.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] (X Y Z U V W : SmoothSite (Spec (.of k)))
  (a : pullback (C := Scheme) X.hom Y.hom)
  (b : pullback (C := Scheme) Y.hom Z.hom)
  (c : pullback (C := Scheme) U.hom V.hom)
  (d : pullback (C := Scheme) V.hom W.hom)

local notation "I" => correspondenceIncidence X.hom Y.hom Z.hom a b
local notation "J" => correspondenceIncidence U.hom V.hom W.hom c d
local notation "F" => correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom
local notation "G" => correspondenceIntersectionAmbientToField k U.hom V.hom W.hom
local notation "p" => correspondenceIncidenceAmbientInclusion X.hom Y.hom Z.hom a b
local notation "q" => correspondenceIncidenceAmbientInclusion U.hom V.hom W.hom c d
local notation "r" => correspondenceSupportProductInclusion X.hom Y.hom Z.hom a b
local notation "s" => correspondenceSupportProductInclusion U.hom V.hom W.hom c d
local notation "δ" => correspondenceTripleInclusion X.hom Y.hom Z.hom
local notation "ε" => correspondenceTripleInclusion U.hom V.hom W.hom
local notation "leftTripleBase" => correspondenceTripleMiddle X.hom Y.hom Z.hom ≫ Y.hom
local notation "rightTripleBase" => correspondenceTripleMiddle U.hom V.hom W.hom ≫ V.hom
local notation "uS" => correspondenceIncidenceToSupportProduct X.hom Y.hom Z.hom a b
local notation "vS" => correspondenceIncidenceToSupportProduct U.hom V.hom W.hom c d
local notation "u'" => correspondenceIncidenceInclusion X.hom Y.hom Z.hom a b
local notation "v'" => correspondenceIncidenceInclusion U.hom V.hom W.hom c d
local notation "P" => pullback (C := Scheme) (p ≫ F) (q ≫ G)
local notation "Q" => pullback (r ≫ F) (s ≫ G)
local notation "D" => pullback (δ ≫ F) (ε ≫ G)
set_option quotPrecheck false in
local notation "f" => (SmoothSite.product X U).hom
set_option quotPrecheck false in
local notation "g" => (SmoothSite.product Y V).hom
set_option quotPrecheck false in
local notation "h" => (SmoothSite.product Z W).hom
local notation "H" => correspondenceExteriorWholeSupportProduct (k := k) X Y Z U V W a b c d
local notation "L" => correspondenceExteriorWholeIncidence (k := k) X Y Z U V W a b c d
local notation "i" => correspondenceExteriorWholeIncidenceToSupport (k := k) X Y Z U V W a b c d
local notation "j" => correspondenceExteriorWholeIncidenceInclusion (k := k) X Y Z U V W a b c d
local notation "m" => correspondenceExteriorWholeSupportInclusion (k := k) X Y Z U V W a b c d
local notation "ambientIso" => correspondenceIntersectionAmbientProductIso (k := k) X Y Z U V W
local notation "t" => correspondenceTripleInclusion f g h

/-- Rewriting the two original incidence structure maps as ambient composites. -/
def correspondenceIncidenceOverAmbientIso :
    P ≅ correspondenceIncidenceProduct X Y Z U V W a b c d :=
  pullback.congrHom (correspondenceIncidenceAmbientInclusion_base X Y Z a b)
    (correspondenceIncidenceAmbientInclusion_base U V W c d)

/-- The product of the original incidence inclusions becomes the whole product-support incidence. -/
def correspondenceWholeIncidenceIso : P ≅ L :=
  correspondenceIncidenceOverAmbientIso X Y Z U V W a b c d ≪≫
    correspondenceIncidenceProductIso X Y Z U V W a b c d

theorem correspondenceWholeIncidenceIso_ambient :
    Scheme.Hom.productClosedMap F G p q ≫ (ambientIso).hom =
      (correspondenceWholeIncidenceIso X Y Z U V W a b c d).hom ≫ j ≫ t := by
  have h' : Scheme.Hom.productClosedMap F G p q =
      (correspondenceIncidenceOverAmbientIso X Y Z U V W a b c d).hom ≫
        correspondenceIncidenceProductAmbientMap X Y Z U V W a b c d := by
    apply pullback.hom_ext <;>
      simp only [Scheme.Hom.productClosedMap, pullback.map, pullback.lift_fst,
        pullback.lift_snd, Category.assoc, correspondenceIncidenceProductAmbientMap_fst,
        correspondenceIncidenceProductAmbientMap_snd, correspondenceIncidenceOverAmbientIso,
        pullback.congrHom_hom, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
        Category.id_comp]
  calc
    _ = (correspondenceIncidenceOverAmbientIso X Y Z U V W a b c d).hom ≫
        correspondenceIncidenceProductAmbientMap X Y Z U V W a b c d ≫ (ambientIso).hom :=
      (congrArg (· ≫ (ambientIso).hom) h').trans (Category.assoc _ _ _)
    _ = _ := by
      rw [correspondenceIncidenceProductIso_ambient]
      simp only [correspondenceWholeIncidenceIso, Iso.trans_hom,
        correspondenceExteriorWholeIncidenceAmbientInclusion, Category.assoc]

local notation "α" => exteriorSupportTargetProjection X Y (integralComponentAt a)
local notation "β" => exteriorSupportSourceProjection Y Z (integralComponentAt b)
local notation "γ" => exteriorSupportTargetProjection U V (integralComponentAt c)
local notation "η" => exteriorSupportSourceProjection V W (integralComponentAt d)
local notation "l" => correspondenceExteriorTarget (k := k) X Y U V (integralComponentAt a)
  (integralComponentAt c)
local notation "rightSupport" =>
  correspondenceExteriorSource (k := k) Y Z V W (integralComponentAt b)
  (integralComponentAt d)

/-- The product of the two original full support products, in the literal order of the
native tensor ambient's whole support product. -/
def correspondenceWholeSupportIso : Q ≅ H := by
  let e₀ := pullback.congrHom
    (show r ≫ F = pullback.fst (α ≫ Y.hom) (β ≫ Y.hom) ≫ (α ≫ Y.hom) by
      simp only [correspondenceIntersectionAmbientToField, Category.assoc,
        correspondenceSupportProductInclusion_snd_assoc]
      exact (@pullback.condition _ _ _ _ _ (α ≫ Y.hom) (β ≫ Y.hom) _).symm)
    (show s ≫ G = pullback.fst (γ ≫ V.hom) (η ≫ V.hom) ≫ (γ ≫ V.hom) by
      simp only [correspondenceIntersectionAmbientToField, Category.assoc,
        correspondenceSupportProductInclusion_snd_assoc]
      exact (@pullback.condition _ _ _ _ _ (γ ≫ V.hom) (η ≫ V.hom) _).symm)
  let e₁ := pullbackFourShuffleIso (α ≫ Y.hom) (β ≫ Y.hom) (γ ≫ V.hom) (η ≫ V.hom)
  let e₂ := correspondenceExteriorTargetBaseIso (k := k) X Y U V a c
  let aL := pullback.fst (α ≫ Y.hom) (γ ≫ V.hom) ≫ (α ≫ Y.hom)
  let aR := pullback.fst (β ≫ Y.hom) (η ≫ V.hom) ≫ (β ≫ Y.hom)
  have hh : e₂.inv ≫ l = pullbackProductFirstMap α γ Y.hom V.hom :=
    correspondenceExteriorTargetBaseIso_inv_target X Y U V a c
  have haL : aL = e₂.inv ≫ (l ≫ g) := by
    change aL = e₂.inv ≫ l ≫ pullback.fst Y.hom V.hom ≫ Y.hom
    rw [reassoc_of% hh]
    have hfst : pullbackProductFirstMap α γ Y.hom V.hom ≫ pullback.fst Y.hom V.hom =
        pullback.fst (α ≫ Y.hom) (γ ≫ V.hom) ≫ α := pullback.lift_fst _ _ _
    exact (reassoc_of% hfst) Y.hom |>.symm
  have haR : aR = rightSupport ≫ g := by
    change aR = rightSupport ≫ pullback.fst Y.hom V.hom ≫ Y.hom
    exact (correspondenceExteriorSource_fst_assoc Y Z V W
      (integralComponentAt b) (integralComponentAt d) Y.hom).symm
  let mapSupport : pullback aL aR ⟶ H := pullback.map aL aR
    (l ≫ g) (rightSupport ≫ g) e₂.inv (𝟙 _) (𝟙 _) ((Category.comp_id _).trans haL)
    ((Category.comp_id _).trans (haR.trans (Category.id_comp _).symm))
  let : IsIso mapSupport := by
    dsimp only [mapSupport]
    infer_instance
  let e₃ := asIso mapSupport
  exact e₀ ≪≫ e₁ ≪≫ e₃

/-- The pullback presentation using the structure maps of the two triple products. -/
def tripleBaseIso : D ≅ pullback leftTripleBase rightTripleBase :=
  pullback.congrHom (by
    simp [correspondenceIntersectionAmbientToField, correspondenceTripleMiddle,
      Category.assoc, ← pullback.condition_assoc]) (by
    simp [correspondenceIntersectionAmbientToField, correspondenceTripleMiddle,
      Category.assoc, ← pullback.condition_assoc])

/-- The product of the two native diagonal domains, in the order of the native triple product. -/
def correspondenceWholeTripleIso : D ≅ correspondenceTripleProduct f g h := by
  let e₀ := tripleBaseIso X Y Z U V W
  let e₁ := pullbackProductInterchangeIso
    (pullback.snd X.hom Y.hom) (pullback.fst Y.hom Z.hom)
    (pullback.snd U.hom V.hom) (pullback.fst V.hom W.hom) Y.hom V.hom
  let e₂ := (pullback.congrHom (@pullback.condition _ _ _ _ _ X.hom Y.hom _).symm
    (@pullback.condition _ _ _ _ _ U.hom V.hom _).symm) ≪≫ correspondenceExteriorShuffle X Y U V
  let e₃ := (correspondenceExteriorShuffle Y Z V W)
  refine e₀ ≪≫ e₁ ≪≫ asIso (pullback.map _ _ (pullback.snd f g) (pullback.fst g h)
    e₂.hom e₃.hom (𝟙 _) ?_ ?_)
  · rw [Category.comp_id]
    apply pullback.hom_ext <;>
      simp [e₂, correspondenceExteriorShuffle, pullbackProductFirstMap, Category.assoc]
  · rw [Category.comp_id]
    apply pullback.hom_ext <;>
      simp [e₃, correspondenceExteriorShuffle, pullbackProductSecondMap, Category.assoc]

set_option maxHeartbeats 1200000 in
-- The product pullbacks have eight original projection maps to check.
/-- The whole support product isomorphism commutes with the actual ambient inclusions. -/
theorem correspondenceWholeSupportIso_ambient :
    Scheme.Hom.productClosedMap F G r s ≫ (ambientIso).hom =
      (correspondenceWholeSupportIso X Y Z U V W a b c d).hom ≫ m := by
  apply (cancel_mono (ambientIso).inv).mp
  have hfst : (ambientIso).inv ≫ pullback.fst F G =
      correspondenceIntersectionAmbientMap (SmoothSite.productFst X U)
        (SmoothSite.productFst Y V) (SmoothSite.productFst Z W) := by
    apply (cancel_epi (ambientIso).hom).mp
    simpa only [Iso.hom_inv_id_assoc] using
      (correspondenceIntersectionAmbientProductIso_first X Y Z U V W).symm
  have hsnd : (ambientIso).inv ≫ pullback.snd F G =
      correspondenceIntersectionAmbientMap (SmoothSite.productSnd X U)
        (SmoothSite.productSnd Y V) (SmoothSite.productSnd Z W) := by
    apply (cancel_epi (ambientIso).hom).mp
    simpa only [Iso.hom_inv_id_assoc] using
      (correspondenceIntersectionAmbientProductIso_second X Y Z U V W).symm
  apply pullback.hom_ext
  · simp only [Category.assoc, hfst, correspondenceIntersectionAmbientProductIso_first]
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [correspondenceWholeSupportIso, correspondenceExteriorWholeSupportInclusion,
        correspondenceIntersectionAmbientMap, correspondenceIntersectionAmbientSmoothIso,
        correspondenceExteriorInclusion, correspondenceExteriorSource, correspondenceExteriorTarget,
        correspondenceExteriorTargetBaseIso, pullback.congrHom_hom, pullback.congrHom_inv,
        pullback.map,
        Scheme.Hom.productClosedMap, SmoothSite.productMap, SmoothSite.productLift,
        SmoothSite.productFst, SmoothSite.productSnd, Category.assoc] <;> rfl
  · simp only [Category.assoc, hsnd, correspondenceIntersectionAmbientProductIso_second]
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [correspondenceWholeSupportIso, correspondenceExteriorWholeSupportInclusion,
        correspondenceIntersectionAmbientMap, correspondenceIntersectionAmbientSmoothIso,
        correspondenceExteriorInclusion, correspondenceExteriorSource, correspondenceExteriorTarget,
        correspondenceExteriorTargetBaseIso, pullback.congrHom_hom, pullback.congrHom_inv,
        pullback.map,
        Scheme.Hom.productClosedMap, SmoothSite.productMap, SmoothSite.productLift,
        SmoothSite.productFst, SmoothSite.productSnd, Category.assoc] <;> rfl

-- Fully expanding the eight pullback projections exposes their literal lift equations.
set_option linter.flexible false in
/-- The product of diagonal inclusions is the actual middle diagonal of the tensor. -/
theorem correspondenceWholeTripleIso_ambient :
    Scheme.Hom.productClosedMap F G δ ε ≫ (ambientIso).hom =
      (correspondenceWholeTripleIso X Y Z U V W).hom ≫ t := by
  apply (cancel_mono (ambientIso).inv).mp
  have hfst : (ambientIso).inv ≫ pullback.fst F G =
      correspondenceIntersectionAmbientMap (SmoothSite.productFst X U)
        (SmoothSite.productFst Y V) (SmoothSite.productFst Z W) := by
    apply (cancel_epi (ambientIso).hom).mp
    simpa only [Iso.hom_inv_id_assoc] using
      (correspondenceIntersectionAmbientProductIso_first X Y Z U V W).symm
  have hsnd : (ambientIso).inv ≫ pullback.snd F G =
      correspondenceIntersectionAmbientMap (SmoothSite.productSnd X U)
        (SmoothSite.productSnd Y V) (SmoothSite.productSnd Z W) := by
    apply (cancel_epi (ambientIso).hom).mp
    simpa only [Iso.hom_inv_id_assoc] using
      (correspondenceIntersectionAmbientProductIso_second X Y Z U V W).symm
  apply pullback.hom_ext
  · simp only [Category.assoc, hfst, correspondenceIntersectionAmbientProductIso_first]
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [correspondenceWholeTripleIso, correspondenceIntersectionAmbientMap,
        correspondenceIntersectionAmbientSmoothIso, correspondenceExteriorShuffle,
        pullbackProductInterchangeIso, pullbackProductInterchangeHom, pullback.congrHom_hom,
        pullback.map, Scheme.Hom.productClosedMap, SmoothSite.productMap, SmoothSite.productLift,
        SmoothSite.productFst, SmoothSite.productSnd, Category.assoc,
        correspondenceTripleMiddle, tripleBaseIso] <;>
      exact (pullback.lift_fst_assoc _ _ _ _).symm
  · simp only [Category.assoc, hsnd, correspondenceIntersectionAmbientProductIso_second]
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [correspondenceWholeTripleIso, correspondenceIntersectionAmbientMap,
        correspondenceIntersectionAmbientSmoothIso, correspondenceExteriorShuffle,
        pullbackProductInterchangeIso, pullbackProductInterchangeHom, pullback.congrHom_hom,
        pullback.map, Scheme.Hom.productClosedMap, SmoothSite.productMap, SmoothSite.productLift,
        SmoothSite.productFst, SmoothSite.productSnd, Category.assoc,
        correspondenceTripleMiddle, tripleBaseIso] <;>
      exact (pullback.lift_snd_assoc _ _ _ _).symm

private def isoStalkOverPoint {A A' : Scheme.{u}} (e : A ≅ A')
    (x : A) (y : A') (comm : y = (e).hom x) : A'.presheaf.stalk y ≅ A.presheaf.stalk x :=
  A'.presheaf.stalkCongr (.of_eq comm) ≪≫ asIso (e.hom.stalkMap x)

private theorem transportedClosedStalkMap_congr
    {A A' B B' : Scheme.{u}} (a : A ⟶ B) (a' : A' ⟶ B')
    (e : B ≅ B') (e' : A ≅ A') (comm : a ≫ (e).hom = e'.hom ≫ a')
    (x : A) (x' : A') (point : B) (point' : B')
    (hp : point = a x) (hp' : point' = a' x') (he : point' = (e).hom point) (he' : x' = e'.hom x) :
    (isoStalkOverPoint e' x x' he').hom.hom.comp (transportedClosedStalkMap a' x' point' hp') =
      (transportedClosedStalkMap a x point hp).comp
        (isoStalkOverPoint e point point' he).hom.hom := by
  subst point point' x'
  have hmap := Scheme.Hom.stalkMap_congr_hom (e'.hom ≫ a') (a ≫ (e).hom) comm.symm x
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hmap
  simp only [transportedClosedStalkMap, isoStalkOverPoint, Iso.trans_hom, asIso_hom,
    TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] at hmap ⊢
  rw [← Category.assoc] at hmap
  exact congrArg CommRingCat.Hom.hom hmap

section Coefficients

variable [PerfectField k]
  (ha : IsFiniteCorrespondencePoint X.hom Y.hom a)
  (hb : IsFiniteCorrespondencePoint Y.hom Z.hom b)
  (hc : IsFiniteCorrespondencePoint U.hom V.hom c)
  (hd : IsFiniteCorrespondencePoint V.hom W.hom d)

local notation "eI" => correspondenceWholeIncidenceIso X Y Z U V W a b c d
local notation "eS" => correspondenceWholeSupportIso X Y Z U V W a b c d
local notation "eT" => correspondenceWholeTripleIso X Y Z U V W
local notation "mp" => Scheme.Hom.productClosedMap F G p q
local notation "ms" => Scheme.Hom.productClosedMap F G r s
local notation "mt" => Scheme.Hom.productClosedMap F G δ ε
local notation "hs" => (correspondenceIncidence_ambient_comm X.hom Y.hom Z.hom a b)
local notation "hs'" => (correspondenceIncidence_ambient_comm U.hom V.hom W.hom c d)
local notation "ps" => productIntersectionMap F G r s p q uS vS hs hs'
local notation "pt" => productIntersectionMap F G δ ε p q u' v' rfl rfl

set_option quotPrecheck false in
local notation "sq" => correspondenceExteriorWholeIncidence_isPullback (k := k) X Y Z U V W a b c d

variable (x : genericPoints (pullback (C := Scheme)
  (correspondenceIncidenceAmbientInclusion X.hom Y.hom Z.hom a b ≫
    correspondenceIntersectionAmbientToField k X.hom Y.hom Z.hom)
  (correspondenceIncidenceAmbientInclusion U.hom V.hom W.hom c d ≫
    correspondenceIntersectionAmbientToField k U.hom V.hom W.hom)))

set_option quotPrecheck false in
local notation "x₁" => pullback.fst (p ≫ F) (q ≫ G) x.val
set_option quotPrecheck false in
local notation "x₂" => pullback.snd (p ≫ F) (q ≫ G) x.val

private theorem transportedClosedStalkMap_refl {A B : Scheme.{u}} (i' : A ⟶ B) (x' : A) :
    transportedClosedStalkMap i' x' (i' x') rfl = (i'.stalkMap x').hom := by
  simp only [transportedClosedStalkMap, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

private abbrev transportedIncidenceTor {A B C : Scheme.{u}}
    (f' : A ⟶ Spec (.of k)) (g' : B ⟶ Spec (.of k)) (h' : C ⟶ Spec (.of k))
    (a' : pullback (C := Scheme) f' g') (b' : pullback (C := Scheme) g' h')
    (y : correspondenceIncidence f' g' h' a' b') (n : ℕ) :=
  ((Tor (ModuleCat (correspondenceIncidenceAmbientStalk f' g' h' a' b' y)) n).obj
    (correspondenceIncidenceSupportStalkModule f' g' h' a' b' y)).obj
    ((ModuleCat.restrictScalars (transportedClosedStalkMap (correspondenceTripleInclusion f' g' h')
      (correspondenceIncidenceInclusion f' g' h' a' b' y)
      (correspondenceIncidenceAmbientInclusion f' g' h' a' b' y) rfl)).obj
      (ModuleCat.of _ ((correspondenceTripleProduct f' g' h').presheaf.stalk
        (correspondenceIncidenceInclusion f' g' h' a' b' y))))

omit [PerfectField k] in
private theorem transportedIncidenceTor_eq {A B C : Scheme.{u}}
    (f' : A ⟶ Spec (.of k)) (g' : B ⟶ Spec (.of k)) (h' : C ⟶ Spec (.of k))
    (a' : pullback (C := Scheme) f' g') (b' : pullback (C := Scheme) g' h')
    (y : correspondenceIncidence f' g' h' a' b') (n : ℕ) :
    transportedIncidenceTor f' g' h' a' b' y n = correspondenceIncidenceTor f' g' h' a' b' y n := by
  let x' := correspondenceIncidenceInclusion f' g' h' a' b' y
  let j' := correspondenceTripleInclusion f' g' h'
  let A₀ := (correspondenceIntersectionAmbient f' g' h').presheaf.stalk (j' x')
  let B₀ := (correspondenceTripleProduct f' g' h').presheaf.stalk x'
  let T (scalar : A₀ →+* B₀) : ModuleCat A₀ := ((Tor (ModuleCat A₀) n).obj
    (correspondenceIncidenceSupportStalkModule f' g' h' a' b' y)).obj
    ((ModuleCat.restrictScalars scalar).obj (ModuleCat.of B₀ B₀))
  exact congrArg T (transportedClosedStalkMap_refl j' x')

/-- The first projected generic point is the original incidence generic. -/
def correspondenceWholeIncidenceFirstGeneric : genericPoints I :=
  ⟨x₁, mem_genericPoints_of_flat (pullback.fst (p ≫ F) (q ≫ G)) x.property⟩

/-- The second projected generic point is the original incidence generic. -/
def correspondenceWholeIncidenceSecondGeneric : genericPoints J :=
  ⟨x₂, mem_genericPoints_of_flat (pullback.snd (p ≫ F) (q ≫ G)) x.property⟩

omit [PerfectField k] in
private theorem supportMap_iso
    [IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a))]
    [IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b))]
    [IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c))]
    [IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d))] :
    ps ≫ (eS).hom = (eI).hom ≫ i := by
  apply (cancel_mono m).mp
  calc
    (ps ≫ (eS).hom) ≫ m = ps ≫ ms ≫ (ambientIso).hom :=
      (Category.assoc _ _ _).trans
        (congrArg (ps ≫ ·) (correspondenceWholeSupportIso_ambient X Y Z U V W a b c d).symm)
    _ = mp ≫ (ambientIso).hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (ambientIso).hom)
          (productIntersectionMap_eq F G r s p q uS vS hs hs').symm)
    _ = ((eI).hom ≫ i) ≫ m :=
      (correspondenceWholeIncidenceIso_ambient X Y Z U V W a b c d).trans
        ((congrArg ((eI).hom ≫ ·) (sq).w.symm).trans (Category.assoc _ _ _).symm)

omit [PerfectField k] in
private theorem tripleMap_iso :
    pt ≫ (eT).hom = (eI).hom ≫ j := by
  apply (cancel_mono t).mp
  calc
    (pt ≫ (eT).hom) ≫ t = pt ≫ mt ≫ (ambientIso).hom :=
      (Category.assoc _ _ _).trans
        (congrArg (pt ≫ ·) (correspondenceWholeTripleIso_ambient X Y Z U V W).symm)
    _ = mp ≫ (ambientIso).hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (ambientIso).hom)
          (productIntersectionMap_eq F G δ ε p q u' v' rfl rfl).symm)
    _ = _ := (correspondenceWholeIncidenceIso_ambient X Y Z U V W a b c d).trans
      (Category.assoc _ _ _).symm

/-- An actual product-incidence generic point transported into the whole tensor incidence. -/
def correspondenceWholeIncidenceGeneric : genericPoints L :=
  ⟨(eI).hom x.val, mem_genericPoints_of_flat (eI).hom x.property⟩

set_option maxHeartbeats 1200000 in
-- The scalar actions are checked at the original points of all three ambient diagrams.
include ha hb hc hd in
/-- The whole support's actual local Tor coefficient retains both original signed coefficients. -/
theorem structureTorCoefficient_wholeIncidence :
    let x' := correspondenceWholeIncidenceGeneric X Y Z U V W a b c d x
    structureTorCoefficient (cartesianIntersectionGenericStalkMap sq x')
      ((t).stalkMap (j x'.val)).hom =
      correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom a b
        (correspondenceWholeIncidenceFirstGeneric X Y Z U V W a b c d x) *
      correspondenceIncidenceTorCoefficient k U.hom V.hom W.hom c d
        (correspondenceWholeIncidenceSecondGeneric X Y Z U V W a b c d x) := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  let x' := correspondenceWholeIncidenceGeneric X Y Z U V W a b c d x
  let Hx := t (j x'.val)
  let Gx := mp x.val
  let ξ := correspondenceWholeIncidenceFirstGeneric X Y Z U V W a b c d x
  let ζ := correspondenceWholeIncidenceSecondGeneric X Y Z U V W a b c d x
  have h₁ : Hx = (ambientIso).hom Gx :=
    (congrArg (fun m' : P ⟶ correspondenceIntersectionAmbient f g h => m' x.val)
      (correspondenceWholeIncidenceIso_ambient X Y Z U V W a b c d)).symm
  have h₂ : i x'.val = (eS).hom (ps x.val) :=
    (congrArg (fun m' : P ⟶ H => m' x.val)
      (supportMap_iso X Y Z U V W a b c d)).symm
  have h₃ : j x'.val = (eT).hom (pt x.val) :=
    (congrArg (fun m' : P ⟶ correspondenceTripleProduct f g h => m' x.val)
      (tripleMap_iso X Y Z U V W a b c d)).symm
  let hS := productIntersectionMap_point_eq F G r s p q uS vS hs hs' x
  let hT := productIntersectionMap_point_eq F G δ ε p q u' v' rfl rfl x
  let αP := transportedClosedStalkMap ms (ps x.val) Gx hS
  let βP := transportedClosedStalkMap mt (pt x.val) Gx hT
  let wholeSupportScalar := cartesianIntersectionGenericStalkMap sq x'
  let wholeTripleScalar := ((t).stalkMap (j x'.val)).hom
  have hα : (isoStalkOverPoint eS (ps x.val) (i x'.val) h₂).hom.hom.comp wholeSupportScalar =
      αP.comp (isoStalkOverPoint ambientIso Gx Hx h₁).hom.hom :=
    transportedClosedStalkMap_congr ms m ambientIso eS
      (correspondenceWholeSupportIso_ambient X Y Z U V W a b c d)
      _ _ _ _ hS (cartesianIntersection_genericPoint_eq sq x') h₁ h₂
  have hβ : (isoStalkOverPoint eT (pt x.val) (j x'.val) h₃).hom.hom.comp wholeTripleScalar =
      βP.comp (isoStalkOverPoint ambientIso Gx Hx h₁).hom.hom := by
    have h₀ : transportedClosedStalkMap t (j x'.val) Hx rfl = wholeTripleScalar :=
      transportedClosedStalkMap_refl t (j x'.val)
    exact (congrArg ((isoStalkOverPoint eT (pt x.val) (j x'.val) h₃).hom.hom.comp ·)
      h₀.symm).trans (transportedClosedStalkMap_congr mt t ambientIso eT
        (correspondenceWholeTripleIso_ambient X Y Z U V W) _ _ _ _ hT rfl h₁ h₃)
  change structureTorCoefficient wholeSupportScalar wholeTripleScalar = _
  rw [structureTorCoefficient_eq_of_ringEquiv wholeSupportScalar wholeTripleScalar αP βP
    (isoStalkOverPoint ambientIso Gx Hx h₁).commRingCatIsoToRingEquiv
    (isoStalkOverPoint eS (ps x.val) (i x'.val) h₂).commRingCatIsoToRingEquiv
    (isoStalkOverPoint eT (pt x.val) (j x'.val) h₃).commRingCatIsoToRingEquiv hα hβ]
  have hfin₁ (n : ℕ) :
      IsFiniteLength (correspondenceIncidenceAmbientStalk X.hom Y.hom Z.hom a b x₁)
        (transportedIncidenceTor X.hom Y.hom Z.hom a b x₁ n) := by
    rw [transportedIncidenceTor_eq]
    exact Module.length_ne_top_iff.mp
      (correspondenceIncidenceTor_length_ne_top (S := Spec (.of k)) X.hom Y.hom Z.hom a b ξ n)
  have hfin₂ (n : ℕ) :
      IsFiniteLength (correspondenceIncidenceAmbientStalk U.hom V.hom W.hom c d x₂)
        (transportedIncidenceTor U.hom V.hom W.hom c d x₂ n) := by
    rw [transportedIncidenceTor_eq]
    exact Module.length_ne_top_iff.mp
      (correspondenceIncidenceTor_length_ne_top (S := Spec (.of k)) U.hom V.hom W.hom c d ζ n)
  have hsupp₁ : {n : ℕ | ¬ IsZero (transportedIncidenceTor X.hom Y.hom Z.hom a b x₁ n)}.Finite :=
    (Set.finite_Iic (correspondenceIncidenceTorDegreeBound k X.hom Y.hom Z.hom a b x₁)).subset
      fun n hn => le_of_not_gt fun hlt => hn ((transportedIncidenceTor_eq
        X.hom Y.hom Z.hom a b x₁ n).symm ▸
          isZero_correspondenceIncidenceTor_of_lt k X.hom Y.hom Z.hom a b x₁ n hlt)
  have hsupp₂ : {n : ℕ | ¬ IsZero (transportedIncidenceTor U.hom V.hom W.hom c d x₂ n)}.Finite :=
    (Set.finite_Iic (correspondenceIncidenceTorDegreeBound k U.hom V.hom W.hom c d x₂)).subset
      fun n hn => le_of_not_gt fun hlt => hn ((transportedIncidenceTor_eq
        U.hom V.hom W.hom c d x₂ n).symm ▸
          isZero_correspondenceIncidenceTor_of_lt k U.hom V.hom W.hom c d x₂ n hlt)
  refine (structureTorCoefficient_product F G r s δ ε p q uS vS u' v' hs hs' rfl rfl x
    hfin₁ hfin₂ hsupp₁ hsupp₂).trans (congrArg₂ (· * ·) ?_ ?_)
  · unfold structureTorCoefficient correspondenceIncidenceTorCoefficient
    refine finsum_congr fun n => ?_
    change (-1 : ℤ) ^ n * (Module.length
      (correspondenceIncidenceAmbientStalk X.hom Y.hom Z.hom a b x₁)
      (transportedIncidenceTor X.hom Y.hom Z.hom a b x₁ n)).toNat = _
    rw [transportedIncidenceTor_eq]
    rfl
  · unfold structureTorCoefficient correspondenceIncidenceTorCoefficient
    refine finsum_congr fun n => ?_
    change (-1 : ℤ) ^ n * (Module.length
      (correspondenceIncidenceAmbientStalk U.hom V.hom W.hom c d x₂)
      (transportedIncidenceTor U.hom V.hom W.hom c d x₂ n)).toNat = _
    rw [transportedIncidenceTor_eq]
    rfl


set_option quotPrecheck false in
local notation "ResidualLeft" => integralComponentAt (pullback.fst F G (mp x.val))
set_option quotPrecheck false in
local notation "ResidualRight" => integralComponentAt (pullback.snd F G (mp x.val))
set_option quotPrecheck false in
local notation "ResidualProduct" => pullback (C := Scheme)
  ((ResidualLeft).subschemeι ≫ F) ((ResidualRight).subschemeι ≫ G)
set_option quotPrecheck false in
local notation "residualMap" =>
  Scheme.Hom.productClosedMap F G (ResidualLeft).subschemeι (ResidualRight).subschemeι

set_option maxHeartbeats 2400000 in
-- Weighted transport checks three ambient diagrams and derives residual stalk finiteness.
omit [PerfectField k] in
include ha hb hc hd in
/-- Over arbitrary fields the whole Tor coefficient retains the residual product length. -/
theorem structureTorCoefficient_wholeIncidence_weighted
    (rpoint : genericPoints ResidualProduct) (hrpoint : residualMap rpoint.val = mp x.val) :
    let x' := correspondenceWholeIncidenceGeneric X Y Z U V W a b c d x
    structureTorCoefficient (cartesianIntersectionGenericStalkMap sq x')
      ((t).stalkMap (j x'.val)).hom =
      correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom a b
        (correspondenceWholeIncidenceFirstGeneric X Y Z U V W a b c d x) *
      correspondenceIncidenceTorCoefficient k U.hom V.hom W.hom c d
        (correspondenceWholeIncidenceSecondGeneric X Y Z U V W a b c d x) *
      ((Module.length ((ResidualProduct).presheaf.stalk rpoint.val)
        ((ResidualProduct).presheaf.stalk rpoint.val)).toNat : ℤ) := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  let x' := correspondenceWholeIncidenceGeneric X Y Z U V W a b c d x
  let Hx := t (j x'.val)
  let Gx := mp x.val
  let ξ := correspondenceWholeIncidenceFirstGeneric X Y Z U V W a b c d x
  let ζ := correspondenceWholeIncidenceSecondGeneric X Y Z U V W a b c d x
  have h₁ : Hx = (ambientIso).hom Gx :=
    (congrArg (fun m' : P ⟶ correspondenceIntersectionAmbient f g h => m' x.val)
      (correspondenceWholeIncidenceIso_ambient X Y Z U V W a b c d)).symm
  have h₂ : i x'.val = (eS).hom (ps x.val) :=
    (congrArg (fun m' : P ⟶ H => m' x.val)
      (supportMap_iso X Y Z U V W a b c d)).symm
  have h₃ : j x'.val = (eT).hom (pt x.val) :=
    (congrArg (fun m' : P ⟶ correspondenceTripleProduct f g h => m' x.val)
      (tripleMap_iso X Y Z U V W a b c d)).symm
  let hS := productIntersectionMap_point_eq F G r s p q uS vS hs hs' x
  let hT := productIntersectionMap_point_eq F G δ ε p q u' v' rfl rfl x
  let αP := transportedClosedStalkMap ms (ps x.val) Gx hS
  let βP := transportedClosedStalkMap mt (pt x.val) Gx hT
  let wholeSupportScalar := cartesianIntersectionGenericStalkMap sq x'
  let wholeTripleScalar := ((t).stalkMap (j x'.val)).hom
  have hα : (isoStalkOverPoint eS (ps x.val) (i x'.val) h₂).hom.hom.comp wholeSupportScalar =
      αP.comp (isoStalkOverPoint ambientIso Gx Hx h₁).hom.hom :=
    transportedClosedStalkMap_congr ms m ambientIso eS
      (correspondenceWholeSupportIso_ambient X Y Z U V W a b c d)
      _ _ _ _ hS (cartesianIntersection_genericPoint_eq sq x') h₁ h₂
  have hβ : (isoStalkOverPoint eT (pt x.val) (j x'.val) h₃).hom.hom.comp wholeTripleScalar =
      βP.comp (isoStalkOverPoint ambientIso Gx Hx h₁).hom.hom := by
    have h₀ : transportedClosedStalkMap t (j x'.val) Hx rfl = wholeTripleScalar :=
      transportedClosedStalkMap_refl t (j x'.val)
    exact (congrArg ((isoStalkOverPoint eT (pt x.val) (j x'.val) h₃).hom.hom.comp ·)
      h₀.symm).trans (transportedClosedStalkMap_congr mt t ambientIso eT
        (correspondenceWholeTripleIso_ambient X Y Z U V W) _ _ _ _ hT rfl h₁ h₃)
  change structureTorCoefficient wholeSupportScalar wholeTripleScalar = _
  rw [structureTorCoefficient_eq_of_ringEquiv wholeSupportScalar wholeTripleScalar αP βP
    (isoStalkOverPoint ambientIso Gx Hx h₁).commRingCatIsoToRingEquiv
    (isoStalkOverPoint eS (ps x.val) (i x'.val) h₂).commRingCatIsoToRingEquiv
    (isoStalkOverPoint eT (pt x.val) (j x'.val) h₃).commRingCatIsoToRingEquiv hα hβ]
  have hfin₁ (n : ℕ) :
      IsFiniteLength (correspondenceIncidenceAmbientStalk X.hom Y.hom Z.hom a b x₁)
        (transportedIncidenceTor X.hom Y.hom Z.hom a b x₁ n) := by
    rw [transportedIncidenceTor_eq]
    exact Module.length_ne_top_iff.mp
      (correspondenceIncidenceTor_length_ne_top (S := Spec (.of k)) X.hom Y.hom Z.hom a b ξ n)
  have hfin₂ (n : ℕ) :
      IsFiniteLength (correspondenceIncidenceAmbientStalk U.hom V.hom W.hom c d x₂)
        (transportedIncidenceTor U.hom V.hom W.hom c d x₂ n) := by
    rw [transportedIncidenceTor_eq]
    exact Module.length_ne_top_iff.mp
      (correspondenceIncidenceTor_length_ne_top (S := Spec (.of k)) U.hom V.hom W.hom c d ζ n)
  have hsupp₁ : {n : ℕ | ¬ IsZero (transportedIncidenceTor X.hom Y.hom Z.hom a b x₁ n)}.Finite :=
    (Set.finite_Iic (correspondenceIncidenceTorDegreeBound k X.hom Y.hom Z.hom a b x₁)).subset
      fun n hn => le_of_not_gt fun hlt => hn ((transportedIncidenceTor_eq
        X.hom Y.hom Z.hom a b x₁ n).symm ▸
          isZero_correspondenceIncidenceTor_of_lt k X.hom Y.hom Z.hom a b x₁ n hlt)
  have hsupp₂ : {n : ℕ | ¬ IsZero (transportedIncidenceTor U.hom V.hom W.hom c d x₂ n)}.Finite :=
    (Set.finite_Iic (correspondenceIncidenceTorDegreeBound k U.hom V.hom W.hom c d x₂)).subset
      fun n hn => le_of_not_gt fun hlt => hn ((transportedIncidenceTor_eq
        U.hom V.hom W.hom c d x₂ n).symm ▸
          isZero_correspondenceIncidenceTor_of_lt k U.hom V.hom W.hom c d x₂ n hlt)
  let : IsLocallyNoetherian (correspondenceIntersectionAmbient f g h) :=
    isLocallyNoetherian_correspondenceIntersectionAmbient (S := Spec (.of k)) f g h
  let : IsLocallyNoetherian (pullback F G) :=
    LocallyOfFiniteType.isLocallyNoetherian (ambientIso).hom
  let : IsLocallyNoetherian ResidualProduct :=
    LocallyOfFiniteType.isLocallyNoetherian residualMap
  refine (structureTorCoefficient_product_weighted_of_isLocallyNoetherian
    F G r s δ ε p q uS vS u' v' hs hs' rfl rfl x rpoint hrpoint
    hfin₁ hfin₂ hsupp₁ hsupp₂).trans ?_
  apply congrArg (fun n : ℤ => n * _)
  refine congrArg₂ (· * ·) ?_ ?_
  · unfold structureTorCoefficient correspondenceIncidenceTorCoefficient
    refine finsum_congr fun n => ?_
    change (-1 : ℤ) ^ n * (Module.length
      (correspondenceIncidenceAmbientStalk X.hom Y.hom Z.hom a b x₁)
      (transportedIncidenceTor X.hom Y.hom Z.hom a b x₁ n)).toNat = _
    rw [transportedIncidenceTor_eq]
    rfl
  · unfold structureTorCoefficient correspondenceIncidenceTorCoefficient
    refine finsum_congr fun n => ?_
    change (-1 : ℤ) ^ n * (Module.length
      (correspondenceIncidenceAmbientStalk U.hom V.hom W.hom c d x₂)
      (transportedIncidenceTor U.hom V.hom W.hom c d x₂ n)).toNat = _
    rw [transportedIncidenceTor_eq]
    rfl

end Coefficients

end Stacks.Chow

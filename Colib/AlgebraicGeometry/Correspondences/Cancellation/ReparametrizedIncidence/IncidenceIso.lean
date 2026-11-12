/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Incidence
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedIncidence.SupportData

/-!
# The native incidence on the two original supports

The free left parameter and the right parameter graph give the original
full scheme incidence, with both outer projections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

/-- The actual middle map of the left native support. -/
abbrev reparametrizedLeftSupportMiddle {k : Type u} [Field k]
    (U X T : SmoothSite (Spec (.of k)))
    (z : pullback (C := Scheme) (SmoothSite.product U T).hom (SmoothSite.product X T).hom) :
    (integralComponentAt z).subscheme ⟶ (SmoothSite.product X T).left :=
  (integralComponentAt z).subschemeι ≫
    pullback.snd (SmoothSite.product U T).hom (SmoothSite.product X T).hom

/-- The actual middle map of the right native support. -/
abbrev reparametrizedRightSupportMiddle {k : Type u} [Field k]
    (X Z T : SmoothSite (Spec (.of k)))
    (w : pullback (C := Scheme) (SmoothSite.product X T).hom (SmoothSite.product Z T).hom) :
    (integralComponentAt w).subscheme ⟶ (SmoothSite.product X T).left :=
  (integralComponentAt w).subschemeι ≫
    pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom

/-- The actual middle map of the original right support with its given parameter. -/
abbrev reparametrizedRightParameterMiddle {k : Type u} [Field k]
    (X T : SmoothSite (Spec (.of k))) {P : Scheme.{u}} (r : P ⟶ X.left)
    (l : P ⟶ T.left) (hl : r ≫ X.hom = l ≫ T.hom) :
    P ⟶ (SmoothSite.product X T).left :=
  pullback.lift r l hl

set_option maxHeartbeats 600000 in
-- The incidence pullback retains both entire native support schemes.
/-- The supplied support isomorphisms identify the two full incidences. -/
def reparametrizedIncidenceSupportIso {k : Type u} [Field k]
    (U X Z T : SmoothSite (Spec (.of k)))
    (z : pullback (C := Scheme) (SmoothSite.product U T).hom (SmoothSite.product X T).hom)
    (w : pullback (C := Scheme) (SmoothSite.product X T).hom (SmoothSite.product Z T).hom)
    {Q P : Scheme.{u}} (p : Q ⟶ X.left) (r : P ⟶ X.left) (l : P ⟶ T.left)
    (hl : r ≫ X.hom = l ≫ T.hom)
    (eQ : pullback (C := Scheme) (p ≫ X.hom) T.hom ≅ (integralComponentAt z).subscheme)
    (eP : P ≅ (integralComponentAt w).subscheme)
    (_hQ : eQ.hom ≫ ((integralComponentAt z).subschemeι ≫
      pullback.snd (SmoothSite.product U T).hom (SmoothSite.product X T).hom) =
        pullbackParameterExtensionMap p X.hom T.hom)
    (_hP : eP.hom ≫ ((integralComponentAt w).subschemeι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom) =
        pullback.lift r l hl) :
    pullback (C := Scheme) (pullbackParameterExtensionMap p X.hom T.hom)
        (reparametrizedRightParameterMiddle X T r l hl) ≅
      pullback (C := Scheme) (reparametrizedLeftSupportMiddle U X T z)
        (reparametrizedRightSupportMiddle X Z T w) :=
  let mid := (SmoothSite.product X T).left
  let a := reparametrizedLeftSupportMiddle U X T z
  let b := reparametrizedRightSupportMiddle X Z T w
  let a₀ : pullback (C := Scheme) (p ≫ X.hom) T.hom ⟶ mid :=
    pullbackParameterExtensionMap p X.hom T.hom
  let b₀ := reparametrizedRightParameterMiddle X T r l hl
  let h₁ : a₀ ≫ 𝟙 mid = eQ.hom ≫ a := (Category.comp_id a₀).trans _hQ.symm
  let h₂ : b₀ ≫ 𝟙 mid = eP.hom ≫ b := (Category.comp_id b₀).trans _hP.symm
  letI : IsIso (𝟙 mid) := (Iso.refl mid).isIso_hom
  let m := pullback.map a₀ b₀ a b eQ.hom eP.hom (𝟙 mid) h₁ h₂
  letI : IsIso m := pullback.map_isIso a₀ b₀ a b eQ.hom eP.hom (𝟙 mid) h₁ h₂
  asIso m

set_option maxHeartbeats 600000 in
-- The two pullback isomorphisms use the literal parameter and support projections.
/-- The native incidence is the actual pullback of the two original middle maps. -/
def reparametrizedIncidenceIso {k : Type u} [Field k]
    (U X Z T : SmoothSite (Spec (.of k)))
    (z : pullback (C := Scheme) (SmoothSite.product U T).hom (SmoothSite.product X T).hom)
    (w : pullback (C := Scheme) (SmoothSite.product X T).hom (SmoothSite.product Z T).hom)
    {Q P : Scheme.{u}} (p : Q ⟶ X.left) (r : P ⟶ X.left) (l : P ⟶ T.left)
    (hl : r ≫ X.hom = l ≫ T.hom)
    (eQ : pullback (C := Scheme) (p ≫ X.hom) T.hom ≅ (integralComponentAt z).subscheme)
    (eP : P ≅ (integralComponentAt w).subscheme)
    (_hQ : eQ.hom ≫ ((integralComponentAt z).subschemeι ≫
      pullback.snd (SmoothSite.product U T).hom (SmoothSite.product X T).hom) =
        pullbackParameterExtensionMap p X.hom T.hom)
    (_hP : eP.hom ≫ ((integralComponentAt w).subschemeι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom) =
        pullback.lift r l hl) :
    pullback (C := Scheme) p r ≅
      pullback (C := Scheme) (reparametrizedLeftSupportMiddle U X T z)
        (reparametrizedRightSupportMiddle X Z T w) :=
  (pullbackParameterIncidence_isPullback p X.hom T.hom r l hl).isoPullback.symm ≪≫
    reparametrizedIncidenceSupportIso U X Z T z w p r l hl eQ eP _hQ _hP

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
local notation3 (prettyPrint := false) "pS" => p ≫ X.hom

local notation3 (prettyPrint := false) "a₀" => pullbackParameterExtensionMap p X.hom T.hom
local notation3 (prettyPrint := false) "b₀" => reparametrizedRightParameterMiddle X T r l hl

set_option maxHeartbeats 600000 in
-- The projection compares the native incidence with its literal support pullback.
@[reassoc (attr := simp)]
theorem reparametrizedIncidenceSupportIso_fst :
    let eI : pullback (C := Scheme) a₀ b₀ ≅ pullback (C := Scheme) a b :=
      @reparametrizedIncidenceSupportIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    eI.hom ≫ pullback.fst (C := Scheme) a b =
      pullback.fst (C := Scheme) a₀ b₀ ≫ (eQ).hom :=
  pullback.lift_fst _ _ _

set_option maxHeartbeats 600000 in
-- The projection compares the native incidence with its literal support pullback.
@[reassoc (attr := simp)]
theorem reparametrizedIncidenceSupportIso_snd :
    let eI : pullback (C := Scheme) a₀ b₀ ≅ pullback (C := Scheme) a b :=
      @reparametrizedIncidenceSupportIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    eI.hom ≫ pullback.snd (C := Scheme) a b =
      pullback.snd (C := Scheme) a₀ b₀ ≫ (eP).hom :=
  pullback.lift_snd _ _ _

set_option maxHeartbeats 600000 in
-- The projection compares the native incidence with its literal support pullback.
/-- The incidence comparison retains the first original support projection. -/
@[reassoc]
theorem reparametrizedIncidenceIso_fst :
    let e : pullback (C := Scheme) p r ≅ pullback (C := Scheme) a b :=
      @reparametrizedIncidenceIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    e.hom ≫ pullback.fst (C := Scheme) a b ≫
      (eQ).inv ≫ pullback.fst pS T.hom = pullback.fst p r := by
  dsimp only
  simp only [reparametrizedIncidenceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    reparametrizedIncidenceSupportIso_fst_assoc, Iso.hom_inv_id_assoc]
  exact (pullbackParameterIncidence_isPullback p X.hom T.hom r l hl).isoPullback_inv_fst

set_option maxHeartbeats 600000 in
-- The projection compares the native incidence with its literal support pullback.
/-- The incidence comparison retains the second original support projection. -/
@[reassoc]
theorem reparametrizedIncidenceIso_snd :
    let e : pullback (C := Scheme) p r ≅ pullback (C := Scheme) a b :=
      @reparametrizedIncidenceIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    e.hom ≫ pullback.snd (C := Scheme) a b =
      pullback.snd p r ≫ (eP).hom := by
  dsimp only
  simp only [reparametrizedIncidenceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    reparametrizedIncidenceSupportIso_snd,
    (pullbackParameterIncidence_isPullback p X.hom T.hom r l hl).isoPullback_inv_snd_assoc]

set_option maxHeartbeats 600000 in
-- The projection compares the native incidence with its literal support pullback.
/-- The parameter seen from the left support is the original right parameter. -/
@[reassoc]
theorem reparametrizedIncidenceIso_parameter :
    let e : pullback (C := Scheme) p r ≅ pullback (C := Scheme) a b :=
      @reparametrizedIncidenceIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    e.hom ≫ pullback.fst (C := Scheme) a b ≫
      (eQ).inv ≫ pullback.snd pS T.hom = pullback.snd p r ≫ l := by
  let e : pullback (C := Scheme) p r ≅ pullback (C := Scheme) a b :=
    @reparametrizedIncidenceIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
  change e.hom ≫ pullback.fst (C := Scheme) a b ≫
    (eQ).inv ≫ pullback.snd pS T.hom = pullback.snd p r ≫ l
  have hleft : a ≫ pullback.snd X.hom T.hom = (eQ).inv ≫ pullback.snd pS T.hom := by
    apply (cancel_epi (eQ).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      reparametrized_left_parameter U X T z p eQ hQ
  have hp := congrArg (fun u => e.hom ≫ u ≫ pullback.snd X.hom T.hom)
    (pullback.condition («f» := a) («g» := b))
  simp only [Category.assoc] at hp
  calc
    _ = e.hom ≫ pullback.fst (C := Scheme) a b ≫
        a ≫ pullback.snd X.hom T.hom := by rw [hleft]
    _ = e.hom ≫ pullback.snd (C := Scheme) a b ≫
        b ≫ pullback.snd X.hom T.hom := hp
    _ = _ := by
      have hproj : e.hom ≫ pullback.snd (C := Scheme) a b =
          pullback.snd p r ≫ eP.hom :=
        reparametrizedIncidenceIso_snd U X Z T z w p r l hl eQ eP hQ hP
      rw [reassoc_of% hproj]
      exact congrArg (pullback.snd p r ≫ ·)
        (reparametrized_right_parameter X Z T w r l hl eP hP)

set_option maxHeartbeats 600000 in
-- The projection compares the native incidence with its literal support pullback.
/-- The target map of the native incidence is its original right support map. -/
@[reassoc]
theorem reparametrizedIncidenceIso_right :
    let e : pullback (C := Scheme) p r ≅ pullback (C := Scheme) a b :=
      @reparametrizedIncidenceIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    e.hom ≫ correspondenceIncidenceRight f g h z w =
      pullback.snd p r ≫ (eP).hom ≫
        (integralComponentAt w).subschemeι ≫ pullback.snd g h := by
  dsimp only
  simp only [correspondenceIncidenceRight, reparametrizedIncidenceIso_snd_assoc]

set_option maxHeartbeats 600000 in
-- The projection compares the native incidence with its literal support pullback.
/-- The native incidence source retains the first original support coordinate. -/
@[reassoc]
theorem reparametrizedIncidenceIso_left_fst (q : Q ⟶ U.left)
    (_hq : (eQ).hom ≫ (integralComponentAt z).subschemeι ≫ pullback.fst f g ≫
      pullback.fst U.hom T.hom = pullback.fst pS T.hom ≫ q) :
    let e : pullback (C := Scheme) p r ≅ pullback (C := Scheme) a b :=
      @reparametrizedIncidenceIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    e.hom ≫
        correspondenceIncidenceLeft f g h z w ≫ pullback.fst U.hom T.hom =
      pullback.fst p r ≫ q := by
  have h' : (integralComponentAt z).subschemeι ≫ pullback.fst f g ≫
      pullback.fst U.hom T.hom = (eQ).inv ≫ pullback.fst pS T.hom ≫ q := by
    apply (cancel_epi (eQ).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using _hq
  dsimp only
  simp only [correspondenceIncidenceLeft, Category.assoc, h',
    reparametrizedIncidenceIso_fst_assoc]

set_option maxHeartbeats 600000 in
-- The projection compares the native incidence with its literal support pullback.
/-- The native incidence source torus is the parameter supplied on the
right support. -/
@[reassoc]
theorem reparametrizedIncidenceIso_left_snd
    (_hq : (eQ).hom ≫ (integralComponentAt z).subschemeι ≫ pullback.fst f g ≫
      pullback.snd U.hom T.hom = pullback.snd pS T.hom) :
    let e : pullback (C := Scheme) p r ≅ pullback (C := Scheme) a b :=
      @reparametrizedIncidenceIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    e.hom ≫
        correspondenceIncidenceLeft f g h z w ≫ pullback.snd U.hom T.hom =
      pullback.snd p r ≫ l := by
  have h' : (integralComponentAt z).subschemeι ≫ pullback.fst f g ≫
      pullback.snd U.hom T.hom = (eQ).inv ≫ pullback.snd pS T.hom := by
    apply (cancel_epi (eQ).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using _hq
  dsimp only
  simp only [correspondenceIncidenceLeft, Category.assoc, h',
    reparametrizedIncidenceIso_parameter]
end Stacks.Chow

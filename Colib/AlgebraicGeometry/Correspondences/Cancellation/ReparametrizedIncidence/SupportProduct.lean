/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.AmbientParameterQuotient
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedIncidence.SupportData

/-!
# The native product of the reparametrized supports

The product of the two actual support isomorphisms preserves the literal
ambient parameter pair.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

/-- The actual structure map of the left native support. -/
abbrev reparametrizedLeftSupportBase {k : Type u} [Field k]
    (U X T : SmoothSite (Spec (.of k)))
    (z : pullback (C := Scheme) (SmoothSite.product U T).hom (SmoothSite.product X T).hom) :
    (integralComponentAt z).subscheme ⟶ Spec (.of k) :=
  (integralComponentAt z).subschemeι ≫
    pullback.snd (SmoothSite.product U T).hom (SmoothSite.product X T).hom ≫
      (SmoothSite.product X T).hom

/-- The actual structure map of the right native support. -/
abbrev reparametrizedRightSupportBase {k : Type u} [Field k]
    (X Z T : SmoothSite (Spec (.of k)))
    (w : pullback (C := Scheme) (SmoothSite.product X T).hom (SmoothSite.product Z T).hom) :
    (integralComponentAt w).subscheme ⟶ Spec (.of k) :=
  (integralComponentAt w).subschemeι ≫
    pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom ≫
      (SmoothSite.product X T).hom

/-- The structure map of the original left support with its free parameter. -/
abbrev reparametrizedFreeSupportBase {k : Type u} [Field k]
    (X T : SmoothSite (Spec (.of k))) {Q : Scheme.{u}} (p : Q ⟶ X.left) :
    pullback (C := Scheme) (p ≫ X.hom) T.hom ⟶ Spec (.of k) :=
  pullback.fst (p ≫ X.hom) T.hom ≫ p ≫ X.hom

set_option maxHeartbeats 600000 in
-- The source and target are the actual iterated and native support pullbacks.
/-- The product of the two actual support isomorphisms. -/
def reparametrizedSupportProductIso {k : Type u} [Field k]
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
    pullback (C := Scheme) (reparametrizedFreeSupportBase X T p) (r ≫ X.hom) ≅
      pullback (C := Scheme) (reparametrizedLeftSupportBase U X T z)
        (reparametrizedRightSupportBase X Z T w) :=
  let base := Spec (.of k)
  let f : (SmoothSite.product U T).left ⟶ base := (SmoothSite.product U T).hom
  let g : (SmoothSite.product X T).left ⟶ base := (SmoothSite.product X T).hom
  let h : (SmoothSite.product Z T).left ⟶ base := (SmoothSite.product Z T).hom
  let first := reparametrizedFreeSupportBase X T p
  let second := r ≫ X.hom
  let leftSupport := reparametrizedLeftSupportBase U X T z
  let rightSupport := reparametrizedRightSupportBase X Z T w
  let hleft : eQ.hom ≫ leftSupport = first := by
    change eQ.hom ≫ (integralComponentAt z).subschemeι ≫ pullback.snd f g ≫
      pullback.fst X.hom T.hom ≫ X.hom = _
    simpa only [first, reparametrizedFreeSupportBase, Category.assoc] using congrArg
      (fun u : pullback (p ≫ X.hom) T.hom ⟶ X.left => u ≫ X.hom)
      (reparametrized_left_projection U X T z p eQ _hQ)
  let hright : eP.hom ≫ rightSupport = second := by
    change eP.hom ≫ (integralComponentAt w).subschemeι ≫ pullback.fst g h ≫
      pullback.fst X.hom T.hom ≫ X.hom = _
    simpa only [second, Category.assoc] using congrArg (fun u : P ⟶ X.left => u ≫ X.hom)
      (reparametrized_right_projection X Z T w r l hl eP _hP)
  let h₁ : first ≫ 𝟙 base = eQ.hom ≫ leftSupport :=
    (Category.comp_id first).trans hleft.symm
  let h₂ : second ≫ 𝟙 base = eP.hom ≫ rightSupport :=
    (Category.comp_id second).trans hright.symm
  let e := pullback.map first second leftSupport rightSupport eQ.hom eP.hom (𝟙 base) h₁ h₂
  letI : IsIso (𝟙 base) := (Iso.refl base).isIso_hom
  letI : IsIso e :=
    pullback.map_isIso first second leftSupport rightSupport eQ.hom eP.hom (𝟙 base) h₁ h₂
  asIso e

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

local notation3 (prettyPrint := false) "aS" => reparametrizedLeftSupportBase U X T z
local notation3 (prettyPrint := false) "bS" => reparametrizedRightSupportBase X Z T w
local notation3 (prettyPrint := false) "pBase" => reparametrizedFreeSupportBase X T p
local notation3 (prettyPrint := false) "pS" => p ≫ X.hom
local notation3 (prettyPrint := false) "rS" => r ≫ X.hom
local notation3 (prettyPrint := false) "i" => correspondenceSupportProductInclusion f g h z w

set_option maxHeartbeats 600000 in
-- The projection identifies the native and iterated full support products.
@[reassoc (attr := simp)]
theorem reparametrizedSupportProductIso_fst :
    let eC : pullback (C := Scheme) pBase rS ≅ pullback (C := Scheme) aS bS :=
      @reparametrizedSupportProductIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    eC.hom ≫
      pullback.fst aS bS =
        pullback.fst (C := Scheme) pBase rS ≫ (eQ).hom :=
  pullback.lift_fst _ _ _

set_option maxHeartbeats 600000 in
-- The projection identifies the native and iterated full support products.
@[reassoc (attr := simp)]
theorem reparametrizedSupportProductIso_snd :
    let eC : pullback (C := Scheme) pBase rS ≅ pullback (C := Scheme) aS bS :=
      @reparametrizedSupportProductIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    eC.hom ≫
      pullback.snd aS bS =
        pullback.snd (C := Scheme) pBase rS ≫ (eP).hom :=
  pullback.lift_snd _ _ _

set_option maxHeartbeats 600000 in
-- The projection identifies the native and iterated full support products.
/-- The native ambient parameter pair pulls back to the actual free parameter
and the given right support parameter. -/
theorem reparametrizedSupportProductIso_parameterPair :
    let eC : pullback (C := Scheme) pBase rS ≅ pullback (C := Scheme) aS bS :=
      @reparametrizedSupportProductIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
    eC.hom ≫ i ≫ exteriorAmbientParameterPair U X Z T =
      pullbackParameterPair pS rS T.hom l hl.symm := by
  apply pullback.hom_ext («f» := T.hom) («g» := T.hom)
  · simp only [Category.assoc, exteriorAmbientParameterPair_fst,
      correspondenceSupportProductInclusion_fst_assoc, reparametrizedSupportProductIso_fst_assoc,
      pullbackParameterPair_fst]
    simpa only [Category.assoc] using congrArg
      (pullback.fst (C := Scheme) pBase rS ≫ ·)
      (reparametrized_left_parameter U X T z p eQ hQ)
  · simp only [Category.assoc, exteriorAmbientParameterPair_snd,
      correspondenceSupportProductInclusion_snd_assoc, reparametrizedSupportProductIso_snd_assoc,
      pullbackParameterPair_snd]
    simpa only [Category.assoc] using congrArg
      (pullback.snd (C := Scheme) pBase rS ≫ ·)
      (reparametrized_right_parameter X Z T w r l hl eP hP)

end Stacks.Chow

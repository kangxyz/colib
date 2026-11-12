/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ParameterGraphRegular
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedIncidence
public import Colib.AlgebraicGeometry.Sites.Smooth.GroupSchemes

/-!
# Regular leading torus equation on the native support product

The actual two native parameter coordinates are the free variable of the
left support and the chosen graph variable of the right support. The
literal diagonal scalar therefore stays regular on their full support
product.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

open Scheme.AffineLineFiber

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

local notation3 (prettyPrint := false) "C" => correspondenceSupportProduct f g h z w
local notation3 (prettyPrint := false) "m" =>
  correspondenceSupportProductInclusion f g h z w ≫ exteriorAmbientParameterPair U X Z T

include p r l hl eQ eP hQ hP in
/-- The original leading scalar has regular pullback to the native support
product with an arbitrary right parameter map. -/
theorem reparametrized_torusScalar_regular (x : C) :
    IsSMulRegular ((C).presheaf.stalk x)
      ((m).stalkMap x (scalar (torusParameterZeroMap τ ξ 1) 0 (m x))) := by
  let pS := p ≫ X.hom
  let rS := r ≫ X.hom
  let eC : pullback («C» := Scheme) (reparametrizedFreeSupportBase X T p) rS ≅ C :=
    @reparametrizedSupportProductIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
  let b := pullback.fst pS rS ≫ pS
  let e : C ≅ pullback («C» := Scheme) b τ :=
    eC.symm ≪≫ pullbackParameterProductIso pS rS τ
  have hpair : m = eC.inv ≫ pullbackParameterPair pS rS τ l hl.symm := by
    have hp := reparametrizedSupportProductIso_parameterPair U X Z T z w p r l hl eQ eP hQ hP
    exact (Iso.eq_inv_comp eC).mpr hp
  apply torusParameterDiagonal_scalar_regular_of_product b (pullback.snd pS rS ≫ l) e m
  · change m ≫ pullback.fst τ τ = e.hom ≫ pullback.snd b τ
    rw [hpair]
    change (eC.inv ≫ pullbackParameterPair pS rS τ l hl.symm) ≫ pullback.fst τ τ =
      (eC.inv ≫ (pullbackParameterProductIso pS rS τ).hom) ≫ pullback.snd b τ
    simpa only [Category.assoc] using congrArg (eC.inv ≫ ·)
      ((pullbackParameterPair_fst pS rS τ l hl.symm).trans
        (pullbackParameterProductIso_hom_parameter pS rS τ).symm)
  · change m ≫ pullback.snd τ τ = e.hom ≫ pullback.fst b τ ≫ pullback.snd pS rS ≫ l
    rw [hpair]
    change (eC.inv ≫ pullbackParameterPair pS rS τ l hl.symm) ≫ pullback.snd τ τ =
      (eC.inv ≫ (pullbackParameterProductIso pS rS τ).hom) ≫
        pullback.fst b τ ≫ pullback.snd pS rS ≫ l
    simpa only [Category.assoc] using congrArg (eC.inv ≫ ·)
      ((pullbackParameterPair_snd pS rS τ l hl.symm).trans
        (pullbackParameterProductIso_hom_second_assoc pS rS τ l).symm)

end Stacks.Chow

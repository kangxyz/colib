/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Retained

/-!
# The actual ambient graph of a power parameter

On the original product, the new source parameter is the source power
divided by the specified unit on the old target. The closed graph
retains both old torus coordinates. Restricting this graph to a support
pulls back the original unit and all original projections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "G(" X ")" => product X T
local notation "V(" Y ")" => torusPowerCutRetainedTarget k Y

variable {X Y : SmoothSite (Spec (.of k))}

set_option quotPrecheck false in
local notation "A" => pullback (C := Scheme) (G(X)).hom (G(Y)).hom
set_option quotPrecheck false in
local notation "B" => pullback (C := Scheme) (G(X)).hom (V(Y)).hom
set_option quotPrecheck false in
local notation "p" => pullback.fst (G(X)).hom (G(Y)).hom
set_option quotPrecheck false in
local notation "q" => pullback.snd (G(X)).hom (G(Y)).hom
set_option quotPrecheck false in
local notation "p'" => pullback.fst (G(X)).hom (V(Y)).hom
set_option quotPrecheck false in
local notation "q'" => pullback.snd (G(X)).hom (V(Y)).hom

variable (n : ℕ)
  (u₀ : (Γ((product Y (multiplicativeGroupObject (Spec (.of k)))).left, ⊤))ˣ)

/-- The new parameter unit on the original support. -/
def torusPowerParameterUnit {P : Scheme.{u}} (i : P ⟶ A) : (Γ(P, ⊤))ˣ :=
  torusSupportCoordinate k (X := X) (i ≫ p) ^ n *
    (Units.map ((i ≫ q).appTop.hom.toMonoidHom) u₀)⁻¹

/-- The power parameter unit restricts by the actual pullback of sections. -/
theorem torusPowerParameterUnit_comp {P E : Scheme.{u}} (i : P ⟶ A) (j : E ⟶ P) :
    torusPowerParameterUnit k n u₀ (j ≫ i) =
      Units.map j.appTop.hom.toMonoidHom (torusPowerParameterUnit k n u₀ i) := by
  have ht : torusSupportCoordinate k (X := X) ((j ≫ i) ≫ p) =
      Units.map j.appTop.hom.toMonoidHom (torusSupportCoordinate k (X := X) (i ≫ p)) := by
    apply Units.ext
    change (((j ≫ i) ≫ p) ≫ (productSnd X T).left).appTop
        (multiplicativeGroupBaseChangeCoordinate Sₖ).val =
      j.appTop (((i ≫ p) ≫ (productSnd X T).left).appTop
        (multiplicativeGroupBaseChangeCoordinate Sₖ).val)
    simp only [Category.assoc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hu : Units.map ((j ≫ i) ≫ q).appTop.hom.toMonoidHom u₀ =
      Units.map j.appTop.hom.toMonoidHom (Units.map (i ≫ q).appTop.hom.toMonoidHom u₀) := by
    apply Units.ext
    change ((j ≫ i) ≫ q).appTop u₀.val = j.appTop ((i ≫ q).appTop u₀.val)
    simp only [Category.assoc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  unfold torusPowerParameterUnit
  rw [map_mul, map_pow, map_inv, ht, hu]

/-- The closed graph of the chosen power parameter on the whole original product. -/
def torusPowerParameterAmbientGraph : A ⟶ B :=
  torusPowerCutRetainedParameterGraph k (𝟙 A) (torusPowerParameterUnit k n u₀ (𝟙 A))

instance torusPowerParameterAmbientGraph_isClosedImmersion :
    IsClosedImmersion (torusPowerParameterAmbientGraph k (X := X) n u₀) :=
  inferInstanceAs (IsClosedImmersion (torusPowerCutRetainedParameterGraph k (𝟙 A)
    (torusPowerParameterUnit k n u₀ (𝟙 A))))

local notation "J" => torusPowerParameterAmbientGraph k (X := X) n u₀

private theorem parameterProjection_source {P : Scheme.{u}} (g : P ⟶ (G(X)).left)
    (a : (Γ(P, ⊤))ˣ) :
    torusPowerCutParameterProjection k g a ≫ pullback.fst X.hom (T).hom =
      g ≫ pullback.fst X.hom (T).hom :=
  torusPowerCutParameterProjection_fst k g a

private theorem parameterProjection_parameter {P : Scheme.{u}} (g : P ⟶ (G(X)).left)
    (a : (Γ(P, ⊤))ˣ) :
    torusPowerCutParameterProjection k g a ≫ pullback.snd X.hom (T).hom =
      (nativeTorusPoint (g ≫ (G(X)).hom) a).left :=
  torusPowerCutParameterProjection_snd k g a

private theorem ambientSchemeIso_target :
    (torusPowerCutAmbientSchemeIso k X Y).hom ≫ pullback.snd X.hom (V(Y)).hom ≫
      pullback.fst (G(Y)).hom (T).hom = q :=
  congrArg (fun f => f.left) (torusPowerCutAmbientIso_hom_target k X Y)

private theorem ambientSchemeIso_torus :
    (torusPowerCutAmbientSchemeIso k X Y).hom ≫ pullback.snd X.hom (V(Y)).hom ≫
      pullback.snd (G(Y)).hom (T).hom = p ≫ pullback.snd X.hom (T).hom :=
  congrArg (fun f => f.left) (torusPowerCutAmbientIso_hom_torus k X Y)

/-- The old source base projection is unchanged by the ambient graph. -/
@[reassoc]
theorem torusPowerParameterAmbientGraph_source :
    J ≫ p' ≫ pullback.fst X.hom (T).hom = p ≫ pullback.fst X.hom (T).hom := by
  rw [torusPowerParameterAmbientGraph, torusPowerCutRetainedParameterGraph_fst_assoc,
    parameterProjection_source, Category.id_comp]

/-- The old target with its torus is retained by the ambient graph. -/
@[reassoc]
theorem torusPowerParameterAmbientGraph_target :
    J ≫ q' ≫ pullback.fst (G(Y)).hom (T).hom = q := by
  rw [torusPowerParameterAmbientGraph, torusPowerCutRetainedParameterGraph_snd_assoc,
    Category.id_comp, ambientSchemeIso_target]

/-- The old source torus is the extra retained target coordinate. -/
@[reassoc]
theorem torusPowerParameterAmbientGraph_torus :
    J ≫ q' ≫ pullback.snd (G(Y)).hom (T).hom = p ≫ pullback.snd X.hom (T).hom := by
  rw [torusPowerParameterAmbientGraph, torusPowerCutRetainedParameterGraph_snd_assoc,
    Category.id_comp, ambientSchemeIso_torus]

/-- The graph on a support is the restriction of the whole ambient graph. -/
theorem torusPowerParameterAmbientGraph_comp {P : Scheme.{u}} (i : P ⟶ A) :
    i ≫ J = torusPowerCutRetainedParameterGraph k i (torusPowerParameterUnit k n u₀ i) := by
  let a := torusPowerParameterUnit k n u₀ (𝟙 A)
  have ha : torusPowerParameterUnit k n u₀ i = Units.map i.appTop.hom.toMonoidHom a := by
    simpa only [Category.comp_id, a] using torusPowerParameterUnit_comp k n u₀ (𝟙 A) i
  apply pullback.hom_ext
  · apply pullback.hom_ext (f := X.hom) (g := (T).hom)
    · simp only [torusPowerParameterAmbientGraph, Category.assoc,
        torusPowerCutRetainedParameterGraph_fst_assoc, parameterProjection_source, Category.id_comp]
    · simp only [torusPowerParameterAmbientGraph, Category.assoc,
        torusPowerCutRetainedParameterGraph_fst_assoc, parameterProjection_parameter,
        Category.id_comp]
      rw [ha]
      let b : A ⟶ Sₖ := p ≫ (G(X)).hom
      change i ≫ (nativeTorusPoint b a).left =
        (nativeTorusPoint ((i ≫ p) ≫ (G(X)).hom) (Units.map i.appTop.hom.toMonoidHom a)).left
      rw [show (i ≫ p) ≫ (G(X)).hom = i ≫ b from Category.assoc _ _ _]
      exact (nativeTorusPoint_comp_left b i a).symm
  · simp only [torusPowerParameterAmbientGraph, Category.assoc,
      torusPowerCutRetainedParameterGraph_snd, Category.id_comp]

/-- The graph map is determined by its new parameter and its retained original
source, target and torus projections. -/
theorem torusPowerParameterAmbientGraph_eq_of_projections {P : Scheme.{u}}
    (i : P ⟶ A) (j : P ⟶ B)
    (hbase : j ≫ p' ≫ pullback.fst X.hom (T).hom = i ≫ p ≫ pullback.fst X.hom (T).hom)
    (hparam : j ≫ p' ≫ pullback.snd X.hom (T).hom =
      (nativeTorusPoint ((i ≫ p) ≫ (G(X)).hom) (torusPowerParameterUnit k n u₀ i)).left)
    (htarget : j ≫ q' ≫ pullback.fst (G(Y)).hom (T).hom = i ≫ q)
    (hretained : j ≫ q' ≫ pullback.snd (G(Y)).hom (T).hom = i ≫ p ≫ pullback.snd X.hom (T).hom) :
    i ≫ J = j := by
  rw [torusPowerParameterAmbientGraph_comp]
  apply pullback.hom_ext
  · apply pullback.hom_ext (f := X.hom) (g := (T).hom)
    · simpa only [Category.assoc, torusPowerCutRetainedParameterGraph_fst_assoc,
        parameterProjection_source] using hbase.symm
    · simpa only [Category.assoc, torusPowerCutRetainedParameterGraph_fst_assoc,
        parameterProjection_parameter] using hparam.symm
  · apply pullback.hom_ext (f := (G(Y)).hom) (g := (T).hom)
    · simpa only [Category.assoc, torusPowerCutRetainedParameterGraph_snd_assoc,
        ambientSchemeIso_target] using htarget.symm
    · simpa only [Category.assoc, torusPowerCutRetainedParameterGraph_snd_assoc,
        ambientSchemeIso_torus] using hretained.symm

end AlgebraicGeometry.Cor

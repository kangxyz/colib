/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection.Naturality
public import Colib.AlgebraicGeometry.Chow.PrincipalSection.Zero
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.NativeChart

/-!
# A Laurent parameter equation and its graph

For global units `a` and `u`, the actual zero scheme of `a - λ * u` on
`P × Gₘ` is the graph of the parameter `a * u⁻¹` over `P`. The isomorphism
retains the inclusion into the product and the original projection to `P`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

open AffineLineFiber

variable {k : Type u} [Field k] {P : Scheme.{u}} (b : P ⟶ Spec (.of k))

set_option quotPrecheck false in
local notation "τ" => (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))
set_option quotPrecheck false in
local notation "ξ" => multiplicativeGroupBaseChangeCoordinate (Spec (.of k))

/-- The native product of a support with a torus parameter. -/
abbrev torusParameterScheme : Scheme.{u} := pullback b τ

local notation "W" => torusParameterScheme b
set_option quotPrecheck false in
local notation "π" => pullback.fst b τ
set_option quotPrecheck false in
local notation "λMap" => pullback.snd b τ
set_option quotPrecheck false in
local notation "Aₚ" => Γ(P, ⊤)

/-- The original forward coordinate on the parameter torus, pulled back to the product. -/
def torusParameterCoordinate : (Γ(W, ⊤))ˣ :=
  Units.map (λMap).appTop.hom.toMonoidHom ξ

/-- The graph of an actual parameter unit over the original support. -/
def torusParameterGraph (a : Aₚˣ) : P ⟶ W :=
  pullback.lift (𝟙 P) (nativeTorusPoint b a).left
    ((Category.id_comp b).trans (nativeTorusPoint_over b a).symm)

@[reassoc (attr := simp)] theorem torusParameterGraph_fst (a : Aₚˣ) :
    torusParameterGraph b a ≫ π = 𝟙 P :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem torusParameterGraph_snd (a : Aₚˣ) :
    torusParameterGraph b a ≫ λMap = (nativeTorusPoint b a).left :=
  pullback.lift_snd _ _ _

instance torusParameterGraph_isClosedImmersion (a : Aₚˣ) :
    IsClosedImmersion (torusParameterGraph b a) := by
  have : IsClosedImmersion (torusParameterGraph b a ≫ π) := by
    rw [torusParameterGraph_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ π

/-- The literal section `a - λ * u` on the parameter product. -/
def torusParameterEquation (a u₀ : Aₚˣ) : Γ(W, ⊤) :=
  (π).appTop a.val - (torusParameterCoordinate b).val * (π).appTop u₀.val

private theorem torusParameterGraph_appTop_fst (a : Aₚˣ) (r : Aₚ) :
    (torusParameterGraph b a).appTop ((π).appTop r) = r := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, torusParameterGraph_fst,
    Scheme.Hom.id_appTop, ConcreteCategory.id_apply]

private theorem torusParameterGraph_appTop_coordinate (a : Aₚˣ) :
    (torusParameterGraph b a).appTop (torusParameterCoordinate b).val = a.val := by
  change (torusParameterGraph b a).appTop ((λMap).appTop (ξ).val) = a.val
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, torusParameterGraph_snd]
  exact congrArg Units.val (nativeTorusPoint_coordinate b a)

private theorem torusParameterGraph_appTop_equation (a u₀ : Aₚˣ) :
    (torusParameterGraph b (a * u₀⁻¹)).appTop (torusParameterEquation b a u₀) = 0 := by
  rw [torusParameterEquation, map_sub, map_mul, torusParameterGraph_appTop_fst,
    torusParameterGraph_appTop_coordinate, torusParameterGraph_appTop_fst, sub_eq_zero]
  change a.val = (((a * u₀⁻¹) * u₀ : Aₚˣ)).val
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-- The actual affine-line map for the parameter equation. -/
abbrev torusParameterZeroMap (a u₀ : Aₚˣ) : W ⟶ Spec (.of (Polynomial k)) :=
  sectionToAffineLine (π ≫ b) (torusParameterEquation b a u₀)

/-- The section map on the graph is the original map to the origin. -/
theorem torusParameterGraph_comp_sectionToAffineLine (a u₀ : Aₚˣ) :
    torusParameterGraph b (a * u₀⁻¹) ≫ torusParameterZeroMap b a u₀ = b ≫ point 0 := by
  rw [← sectionToAffineLine_comp, torusParameterGraph_appTop_equation, sectionToAffineLine_zero,
    torusParameterGraph_fst_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem torusParameterZero_comp_graph (a u₀ : Aₚˣ) :
    (inclusion (torusParameterZeroMap b a u₀) 0 ≫ π) ≫ torusParameterGraph b (a * u₀⁻¹) =
      inclusion (torusParameterZeroMap b a u₀) 0 := by
  let i := inclusion (torusParameterZeroMap b a u₀) 0
  let z := i ≫ π
  let l := i ≫ λMap
  have hzero := section_zero_inclusion_appTop (π ≫ b) (torusParameterEquation b a u₀)
  change i.appTop ((π).appTop a.val - (λMap).appTop (ξ).val * (π).appTop u₀.val) = 0 at hzero
  simp only [map_sub, map_mul, sub_eq_zero, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop] at hzero
  have hunit : Units.map l.appTop.hom.toMonoidHom ξ =
      Units.map z.appTop.hom.toMonoidHom (a * u₀⁻¹) := by
    rw [map_mul, map_inv]
    apply eq_mul_inv_of_mul_eq
    exact Units.ext hzero.symm
  let t : Over.mk (z ≫ b) ⟶ Scheme.asOver (multiplicativeGroupBaseChange (Spec (.of k)))
      (Spec (.of k)) := Over.homMk l (by
    change l ≫ τ = z ≫ b
    simp only [l, z, Category.assoc]
    rw [pullback.condition])
  have hleft := congrArg (fun a => a.left) (NativeTorusPolynomial.nativeTorusPoint_recover
    (z ≫ b) t)
  change (nativeTorusPoint (z ≫ b) (Units.map l.appTop.hom.toMonoidHom ξ)).left = l at hleft
  rw [hunit, nativeTorusPoint_comp_left] at hleft
  apply pullback.hom_ext
  · simp only [Category.assoc, torusParameterGraph_fst, Category.comp_id]
  · simpa only [z, l, Category.assoc, torusParameterGraph_snd] using hleft

set_option backward.isDefEq.respectTransparency false in
/-- The whole zero scheme of `a - λ * u` is the graph of `a * u⁻¹`. -/
def torusParameterGraphZeroIso (a u₀ : Aₚˣ) : P ≅ fiber (torusParameterZeroMap b a u₀) 0 where
  hom := pullback.lift b (torusParameterGraph b (a * u₀⁻¹))
    (torusParameterGraph_comp_sectionToAffineLine b a u₀).symm
  inv := inclusion (torusParameterZeroMap b a u₀) 0 ≫ π
  hom_inv_id := by simp only [pullback.lift_snd_assoc, torusParameterGraph_fst]
  inv_hom_id := by
    apply (cancel_mono (inclusion (torusParameterZeroMap b a u₀) 0)).mp
    rw [Category.assoc, pullback.lift_snd, Category.id_comp]
    exact torusParameterZero_comp_graph b a u₀

/-- The graph isomorphism identifies the actual inclusion into the parameter product. -/
@[reassoc (attr := simp)] theorem torusParameterGraphZeroIso_hom_inclusion (a u₀ : Aₚˣ) :
    (torusParameterGraphZeroIso b a u₀).hom ≫ inclusion (torusParameterZeroMap b a u₀) 0 =
      torusParameterGraph b (a * u₀⁻¹) :=
  pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme

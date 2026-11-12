/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialFractionCuts
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField

/-!
# The original polynomial family in its actual function field

The original open immersion and its native line map transport the same section
and rational function. Native function-field maps are used throughout, with
no replacement of the polynomial product or assumed polynomial fraction identity.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen
open AlgebraicGeometry.PrincipalFamilyEndpointCuts

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

local instance {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, by trivial⟩⟩

local instance {X Y : Scheme.{u}} (j : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpen_range.dense ⟨j (genericPoint X), Set.mem_range_self _⟩⟩

local instance {X Y : Scheme.{u}} (j : X ⟶ Y) [IsIntegral X] [IsOpenImmersion j] :
    Nonempty (j ''ᵁ (⊤ : X.Opens)) :=
  ⟨⟨j (genericPoint X), ⟨genericPoint X, by trivial, rfl⟩⟩⟩

local instance {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    Surjective (projection p) := ⟨fun x => ⟨endpoint p 0 x, by
      change (endpoint p 0 ≫ projection p) x = x
      rw [endpoint_projection]
      rfl⟩⟩

local instance {k : Type u} [Field k] {C W : Scheme.{u}}
    (p : C ⟶ Spec (.of k)) (v : W ⟶ C) [IsOpenImmersion v]
    [IsIntegral W] [IsIntegral (parameterSpace p)] :
    IsIntegral (parameterSpace (v ≫ p)) := by
  have : Nonempty (parameterSpace (v ≫ p)) := ⟨endpoint (v ≫ p) 0 (genericPoint W)⟩
  exact isIntegral_of_isOpenImmersion (lineMap p v)

/-- The actual line map retains the original polynomial coordinate. -/
theorem lineMap_parameter {k : Type u} [Field k] {C W : Scheme.{u}}
    (p : C ⟶ Spec (.of k)) (v : W ⟶ C) :
    (lineMap p v).appTop (parameter p) = parameter (v ≫ p) := by
  rw [parameter, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  simp only [lineMap, pullback.map, pullback.lift_snd, Category.comp_id]
  rfl

/-- Native function-field pullback is functorial for the actual scheme composites. -/
theorem functionFieldMap_comp_native {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (a : X ⟶ Y) (b : Y ⟶ Z) [IsDominant a] [IsDominant b] :
    (a ≫ b).functionFieldMap = b.functionFieldMap ≫ a.functionFieldMap := by
  simp only [Scheme.Hom.functionFieldMap, Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← b.stalkSpecializes_stalkMap_assoc _ _ (specializes_genericPoint_of_isDominant a)]
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- Native function-field pullback agrees with the actual map on global sections. -/
theorem functionFieldMap_global {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (j : X ⟶ Y) [IsDominant j] (a : Γ(Y, ⊤)) :
    j.functionFieldMap (Y.germToFunctionField ⊤ a) =
      X.germToFunctionField ⊤ (j.appTop a) := by
  have htop : j.appLE ⊤ ⊤ (by simp) = j.appTop := by
    unfold Scheme.Hom.appLE
    change j.appTop ≫ X.presheaf.map (𝟙 _) = j.appTop
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [htop] using
    j.functionFieldMap_germToFunctionField (U := ⊤) (V := ⊤) (by simp) a


variable {C W : Scheme.{u}} (v : W ⟶ C) [IsOpenImmersion v]
    [IsIntegral W] [IsIntegral C]

/-- The curve rational function is the original section on its actual open image. -/
def curveRationalFunction (f : Γ(W, ⊤)) : C.functionField :=
  C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f)

/-- Pullback through the original open immersion recovers the unchanged section. -/
theorem curveRationalFunction_pullback (f : Γ(W, ⊤)) :
    v.functionFieldMap (curveRationalFunction v f) = W.germToFunctionField ⊤ f := by
  rw [curveRationalFunction,
    v.functionFieldMap_germToFunctionField (v.preimage_image_eq ⊤).ge,
    ← v.appIso_hom']
  exact congrArg (fun a => W.germToFunctionField ⊤ a)
    (ConcreteCategory.congr_hom (v.appIso ⊤).inv_hom_id f)

variable {k : Type u} [Field k] (p : C ⟶ Spec (.of k))
    [IsIntegral (parameterSpace p)]

omit [IsIntegral C] in
/-- The unit-open germ is the same original polynomial section on the full open image. -/
theorem ambientRationalFunction_eq_ambientSection (f : Γ(W, ⊤))
    [Nonempty (ambientUnitOpen p v f)] :
    ambientRationalFunction p v f =
      (parameterSpace p).germToFunctionField (lineMap p v ''ᵁ ⊤)
        (ambientSection p v f) := by
  rw [ambientRationalFunction, ambientUnitSection_eq_restriction]
  exact (parameterSpace p).presheaf.germ_res_apply
    ((lineMap p v).opensFunctor.map
      (((parameterSpace (v ≫ p)).basicOpen_le (familySection (v ≫ p) f)).hom))
    (genericPoint (parameterSpace p))
    (((genericPoint_spec (parameterSpace p)).mem_open_set_iff
      (ambientUnitOpen p v f).isOpen).mpr (by simpa using
        (inferInstance : Nonempty (ambientUnitOpen p v f)))) (ambientSection p v f)

omit [IsIntegral C] in
/-- The actual line map pulls the original ambient rational function back to the
literal polynomial family section, before any fraction presentation is chosen. -/
theorem ambientRationalFunction_pullback (f : Γ(W, ⊤))
    [Nonempty (ambientUnitOpen p v f)] :
    (lineMap p v).functionFieldMap (ambientRationalFunction p v f) =
      (parameterSpace (v ≫ p)).germToFunctionField ⊤ (familySection (v ≫ p) f) := by
  rw [ambientRationalFunction_eq_ambientSection,
    (lineMap p v).functionFieldMap_germToFunctionField
      ((lineMap p v).preimage_image_eq ⊤).ge,
    ← (lineMap p v).appIso_hom', ambientSection]
  exact congrArg (fun a => (parameterSpace (v ≫ p)).germToFunctionField ⊤ a)
    (ConcreteCategory.congr_hom ((lineMap p v).appIso ⊤).inv_hom_id
      (familySection (v ≫ p) f))

/-- Actual function-field pullbacks respect the polynomial projection square. -/
theorem lineMap_projection_functionField :
    (projection p).functionFieldMap ≫ (lineMap p v).functionFieldMap =
      v.functionFieldMap ≫ (projection (v ≫ p)).functionFieldMap := by
  simp only [← functionFieldMap_comp_native, lineMap_projection]

/-- In the unchanged ambient function field the original family is exactly
`t` times the original curve rational function plus `1-t`. -/
theorem ambientRationalFunction_eq_linear (f : Γ(W, ⊤))
    [Nonempty (ambientUnitOpen p v f)] :
    ambientRationalFunction p v f =
      (parameterSpace p).germToFunctionField ⊤ (parameter p) *
        (projection p).functionFieldMap (curveRationalFunction v f) +
      (1 - (parameterSpace p).germToFunctionField ⊤ (parameter p)) := by
  apply (lineMap p v).functionFieldMap.hom.injective
  rw [ambientRationalFunction_pullback]
  have heval := ConcreteCategory.congr_hom (lineMap_projection_functionField v p)
    (curveRationalFunction v f)
  simp only [CommRingCat.comp_apply] at heval
  simp only [map_add, map_mul, map_sub, map_one]
  rw [functionFieldMap_global, lineMap_parameter, heval, curveRationalFunction_pullback,
    functionFieldMap_global]
  simp only [familySection, map_add, map_mul, map_sub, map_one]


variable {U : Scheme.{u}} (u : U ⟶ C) [IsOpenImmersion u] [IsIntegral U]

/-- The unchanged family pulled to an actual open polynomial chart retains the
original curve rational function through the canonical chart map. -/
theorem ambientRationalFunction_chart_linear (f : Γ(W, ⊤))
    [Nonempty (ambientUnitOpen p v f)] :
    (lineMap p u).functionFieldMap (ambientRationalFunction p v f) =
      (parameterSpace (u ≫ p)).germToFunctionField ⊤ (parameter (u ≫ p)) *
        (projection (u ≫ p)).functionFieldMap (u.functionFieldMap (curveRationalFunction v f)) +
      (1 - (parameterSpace (u ≫ p)).germToFunctionField ⊤ (parameter (u ≫ p))) := by
  rw [ambientRationalFunction_eq_linear]
  simp only [map_add, map_mul, map_sub, map_one]
  rw [functionFieldMap_global, lineMap_parameter]
  have heval := ConcreteCategory.congr_hom (lineMap_projection_functionField u p)
    (curveRationalFunction v f)
  simpa only [CommRingCat.comp_apply] using congrArg
    (fun z => (parameterSpace (u ≫ p)).germToFunctionField ⊤ (parameter (u ≫ p)) * z +
      (1 - (parameterSpace (u ≫ p)).germToFunctionField ⊤ (parameter (u ≫ p)))) heval

/-- A fraction of the original curve function becomes the literal polynomial
numerator divided by the unchanged denominator on the actual polynomial chart.
Only the curve fraction is an input; the polynomial identity is proved. -/
theorem ambientRationalFunction_chart_fraction (f : Γ(W, ⊤))
    [Nonempty (ambientUnitOpen p v f)] (a b : Γ(U, ⊤)) (hb : b ≠ 0)
    (hab : U.germToFunctionField ⊤ a / U.germToFunctionField ⊤ b =
      u.functionFieldMap (curveRationalFunction v f)) :
    (lineMap p u).functionFieldMap (ambientRationalFunction p v f) =
      (parameterSpace (u ≫ p)).germToFunctionField ⊤ (numerator (u ≫ p) a b) /
        (parameterSpace (u ≫ p)).germToFunctionField ⊤ (denominator (u ≫ p) b) := by
  have hbK : U.germToFunctionField ⊤ b ≠ 0 := by
    intro hz
    apply hb
    exact U.germToFunctionField_injective ⊤
      (hz.trans (map_zero (U.germToFunctionField ⊤).hom).symm)
  have hB : (parameterSpace (u ≫ p)).germToFunctionField ⊤
      ((projection (u ≫ p)).appTop b) ≠ 0 := by
    rw [← functionFieldMap_global]
    intro hz
    apply hbK
    exact (projection (u ≫ p)).functionFieldMap.hom.injective
      (hz.trans (map_zero (projection (u ≫ p)).functionFieldMap.hom).symm)
  rw [ambientRationalFunction_chart_linear, ← hab]
  simp only [map_div₀]
  rw [functionFieldMap_global, functionFieldMap_global]
  simp only [numerator, denominator, map_add, map_mul, map_sub, map_one]
  field_simp [hB]


/-- A nonzero original section gives the same nonzero curve rational function. -/
theorem curveRationalFunction_ne_zero (f : Γ(W, ⊤)) (hf : f ≠ 0) :
    curveRationalFunction v f ≠ 0 := by
  intro hz
  have H := curveRationalFunction_pullback v f
  rw [hz, map_zero] at H
  exact hf (W.germToFunctionField_injective ⊤
    (H.symm.trans (map_zero (W.germToFunctionField ⊤).hom).symm))

/-- Construct an actual affine-chart fraction of the original curve function,
prove the original polynomial family's literal fraction identity, and obtain
both full endpoint Tor cuts. No fraction comparison certificate is an input. -/
@[colib_tag "COL-1056", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/FlatPullbackPrincipalDiviso\
    r.lean:585-627"
  "ingredient" "Original local fraction and order as full quotient-length difference; the \
    support and endpoint assembly is proved here."]
theorem exists_chartFraction_endpointTor [IsAffine U] [IsNoetherian U]
    [IsNoetherian (parameterSpace (u ≫ p))]
    (f : Γ(W, ⊤)) (hf : f ≠ 0) [Nonempty (ambientUnitOpen p v f)] :
    ∃ a b : Γ(U, ⊤),
      U.germToFunctionField ⊤ a / U.germToFunctionField ⊤ b =
        u.functionFieldMap (curveRationalFunction v f) ∧
      (lineMap p u).functionFieldMap (ambientRationalFunction p v f) =
        (parameterSpace (u ≫ p)).germToFunctionField ⊤ (numerator (u ≫ p) a b) /
          (parameterSpace (u ≫ p)).germToFunctionField ⊤ (denominator (u ≫ p) b) ∧
      ∀ (x : U) (_hx : Order.coheight x = 1),
        U.presheaf.germ ⊤ x (by trivial)
          ((endpoint (u ≫ p) 0).appTop (numerator (u ≫ p) a b)) ≠ 0 ∧
        U.presheaf.germ ⊤ x (by trivial)
          ((endpoint (u ≫ p) 1).appTop (numerator (u ≫ p) a b)) ≠ 0 ∧
        (∀ c : k, U.presheaf.germ ⊤ x (by trivial)
          ((endpoint (u ≫ p) c).appTop (denominator (u ≫ p) b)) ≠ 0) ∧
        weightedEndpointStalkTor (u ≫ p) 0 x (numerator (u ≫ p) a b) -
          weightedEndpointStalkTor (u ≫ p) 0 x (denominator (u ≫ p) b) = 0 ∧
        weightedEndpointStalkTor (u ≫ p) 1 x (numerator (u ≫ p) a b) -
          weightedEndpointStalkTor (u ≫ p) 1 x (denominator (u ≫ p) b) =
            U.ord (u.functionFieldMap (curveRationalFunction v f)) x := by
  have hF : u.functionFieldMap (curveRationalFunction v f) ≠ 0 := by
    intro hz
    apply curveRationalFunction_ne_zero v f hf
    exact u.functionFieldMap.hom.injective
      (hz.trans (map_zero u.functionFieldMap.hom).symm)
  obtain ⟨a, b, hab, hcuts⟩ := exists_affineFraction_endpointTor (u ≫ p) _ hF
  have hb : b ≠ 0 := by
    intro hb
    apply hF
    simpa only [hb, map_zero, div_zero] using hab.symm
  exact ⟨a, b, hab, ambientRationalFunction_chart_fraction v p u f a b hb hab, hcuts⟩


end AlgebraicGeometry.PrincipalFamilyUnitOpen

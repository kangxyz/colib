/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedProductFamily
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The actual boundary-unit open of a principal polynomial family

The function is literally `t * f + (1 - t)` on the given neighborhood times
the polynomial line. Its unit locus need not be a product open. The entire
original boundary times the line lies in that locus when the original boundary
restriction of `f` is one. Transport to the unchanged ambient product uses the
native open-immersion section isomorphism. No finiteness or principal homotopy
relation is asserted here.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.ComponentFacePlacement`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyLocalFraction`,
`Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamily`.

Adapted from
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/PolynomialFamily/PrincipalFamilyUnitOpen.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.PolynomialSectionPencil

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {R : Type u} [CommRing R] {C W B : Scheme.{u}}

instance (p : C ⟶ Spec (.of R)) (v : W ⟶ C) [IsOpenImmersion v] :
    IsOpenImmersion (parameterMap p v) :=
  MorphismProperty.of_isPullback (parameterMap_isPullback p v) inferInstance

/-- The original numerator of the homotopy, before taking any unit open. -/
def familySection (p : W ⟶ Spec (.of R)) (f : Γ(W, ⊤)) :
    Γ(parameterSpace p, ⊤) :=
  parameter p * (projection p).appTop f + (1 - parameter p)

/-- Normalization holds on the whole original boundary product. -/
theorem boundary_familySection (p : W ⟶ Spec (.of R)) (b : B ⟶ W)
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1) :
    (parameterMap p b).appTop (familySection p f) = 1 := by
  have h : (parameterMap p b).appTop ((projection p).appTop f) = 1 := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      parameterMap_projection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf, map_one]
  simp only [familySection, map_add, map_mul, map_sub, map_one, h, mul_one]
  ring

/-- The actual, possibly non-product, unit open of the literal family section. -/
def unitOpen (p : W ⟶ Spec (.of R)) (f : Γ(W, ⊤)) :
    (parameterSpace p).Opens :=
  (parameterSpace p).basicOpen (familySection p f)

/-- No boundary points are discarded when passing to the unit locus. -/
theorem boundary_mem_unitOpen (p : W ⟶ Spec (.of R)) (b : B ⟶ W)
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1) (x : parameterSpace (b ≫ p)) :
    parameterMap p b x ∈ unitOpen p f := by
  have h : (parameterMap p b) ⁻¹ᵁ unitOpen p f = ⊤ := by
    rw [unitOpen, Scheme.preimage_basicOpen_top, boundary_familySection p b f hf,
      Scheme.basicOpen_one]
  change x ∈ (parameterMap p b) ⁻¹ᵁ unitOpen p f
  rw [h]
  trivial

/-- The section on the unit open is the literal restriction, not a new rational function. -/
def unitSection (p : W ⟶ Spec (.of R)) (f : Γ(W, ⊤)) :
    Γ(parameterSpace p, unitOpen p f) :=
  (parameterSpace p).presheaf.map
    ((parameterSpace p).basicOpen_le (familySection p f)).hom.op (familySection p f)

theorem isUnit_unitSection (p : W ⟶ Spec (.of R)) (f : Γ(W, ⊤)) :
    IsUnit (unitSection p f) :=
  (parameterSpace p).toRingedSpace.isUnit_res_basicOpen (familySection p f)

variable (p : C ⟶ Spec (.of R)) (v : W ⟶ C) [IsOpenImmersion v]

/-- The unit open inside the unchanged original ambient product. -/
def ambientUnitOpen (f : Γ(W, ⊤)) : (parameterSpace p).Opens :=
  parameterMap p v ''ᵁ unitOpen (v ≫ p) f

/-- The exact original section transported along the original open immersion. -/
def ambientUnitSection (f : Γ(W, ⊤)) :
    Γ(parameterSpace p, ambientUnitOpen p v f) :=
  ((parameterMap p v).appIso (unitOpen (v ≫ p) f)).inv (unitSection (v ≫ p) f)

theorem isUnit_ambientUnitSection (f : Γ(W, ⊤)) :
    IsUnit (ambientUnitSection p v f) :=
  (isUnit_unitSection (v ≫ p) f).map
    ((parameterMap p v).appIso (unitOpen (v ≫ p) f)).inv.hom

/-- The complete original boundary product remains inside the original ambient unit open. -/
theorem boundary_mem_ambientUnitOpen (b : B ⟶ W) (f : Γ(W, ⊤))
    (hf : b.appTop f = 1) (x : parameterSpace (b ≫ (v ≫ p))) :
    (parameterMap (v ≫ p) b ≫ parameterMap p v) x ∈ ambientUnitOpen p v f := by
  exact ⟨parameterMap (v ≫ p) b x, boundary_mem_unitOpen (v ≫ p) b f hf x, rfl⟩

/-- A nonempty original boundary supplies an actual point of the ambient unit
open, using the literal zero section of the parameter line. -/
theorem nonempty_ambientUnitOpen_of_boundary (b : B ⟶ W) [Nonempty B]
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1) :
    Nonempty (ambientUnitOpen p v f) := by
  obtain ⟨x⟩ := ‹Nonempty B›
  let y := endpoint (b ≫ (v ≫ p)) 0 x
  exact ⟨⟨(parameterMap (v ≫ p) b ≫ parameterMap p v) y,
    boundary_mem_ambientUnitOpen p v b f hf y⟩⟩

/-- The literal polynomial section on the full original neighborhood image. -/
def ambientSection (f : Γ(W, ⊤)) :
    Γ(parameterSpace p, parameterMap p v ''ᵁ ⊤) :=
  ((parameterMap p v).appIso ⊤).inv (familySection (v ≫ p) f)

/-- Transport and restriction commute for the same polynomial, before taking its germ. -/
theorem ambientUnitSection_eq_restriction (f : Γ(W, ⊤)) :
    ambientUnitSection p v f =
      (parameterSpace p).presheaf.map
        ((parameterMap p v).opensFunctor.map
          (((parameterSpace (v ≫ p)).basicOpen_le
            (familySection (v ≫ p) f)).hom)).op
        (ambientSection p v f) := by
  exact ConcreteCategory.congr_hom
    ((parameterMap p v).appIso_inv_naturality
      (((parameterSpace (v ≫ p)).basicOpen_le (familySection (v ≫ p) f)).hom.op))
    (familySection (v ≫ p) f)

/-- Pulling back recovers exactly the literal polynomial restriction. -/
theorem ambientUnitSection_pullback (f : Γ(W, ⊤)) :
    ((parameterMap p v).appIso (unitOpen (v ≫ p) f)).hom
      (ambientUnitSection p v f) = unitSection (v ≫ p) f := by
  exact ConcreteCategory.congr_hom
    ((parameterMap p v).appIso (unitOpen (v ≫ p) f)).inv_hom_id (unitSection (v ≫ p) f)

/-- The native rational germ belongs to the unchanged ambient product. Integrality
and nonemptiness are explicit; no connected-component assembly is hidden. -/
def ambientRationalFunction [IsIntegral (parameterSpace p)] (f : Γ(W, ⊤))
    [Nonempty (ambientUnitOpen p v f)] : (parameterSpace p).functionField :=
  (parameterSpace p).germToFunctionField (ambientUnitOpen p v f)
    (ambientUnitSection p v f)

end AlgebraicGeometry.PrincipalFamilyUnitOpen

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.PolynomialSectionPencil
end

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.PolynomialSectionPencil
open AlgebraicGeometry.PrincipalFamilyUnitOpen
namespace AlgebraicGeometry.PrincipalFamilyUnitOpen
/-- The complete original boundary cover gives the complete family boundary cover. -/
theorem complement_subset_ambientUnitOpen {R : Type u} [CommRing R]
    {C V W B : Scheme.{u}} (p : C ⟶ Spec (.of R))
    (j : V ⟶ C) (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W)
    (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1) :
    (Set.range (parameterMap p j))ᶜ ⊆ (ambientUnitOpen p v f : Set (parameterSpace p)) := by
  intro x hx
  have hx' : projection p x ∉ Set.range j := by
    rintro ⟨y, hy⟩
    obtain ⟨z, hzx, -⟩ := Scheme.exists_preimage_of_isPullback
      (parameterMap_isPullback p j).flip x y hy.symm
    exact hx ⟨z, hzx⟩
  obtain ⟨y, hy⟩ := hcover hx'
  obtain ⟨z, hzx, hzy⟩ := Scheme.exists_preimage_of_isPullback
    (parameterMap_isPullback p v).flip x (b y) hy.symm
  obtain ⟨w, hwz, -⟩ := Scheme.exists_preimage_of_isPullback
    (parameterMap_isPullback (v ≫ p) b).flip z y hzy
  have hw := boundary_mem_ambientUnitOpen p v b f hf w
  change x ∈ ambientUnitOpen p v f
  simpa only [Scheme.Hom.comp_apply, hwz, hzx] using hw


end AlgebraicGeometry.PrincipalFamilyUnitOpen
end

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedRestriction
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedClosure
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# The derived-saturated image of open restriction

An actual complex belongs to this full subcategory if its derived object is isomorphic to the
restriction of a native Stacks perfect complex vanishing on T. This definition preserves
every original chain
map and does not assert that every perfect complex on the open extends globally.

Adapted from Quillen's `SupportedOpenDerivedImage/Basic.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, with native Mathlib and Stacks objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [HasDerivedCategory.{d} U.Modules]

local notation "R" => Functor.mapHomologicalComplex (restrictFunctor j) (ComplexShape.up ℤ)

/-- Actual complexes derived-isomorphic to restrictions of native supported perfect complexes. -/
def complexObjects : ObjectProperty (CochainComplex U.Modules ℤ) := fun E =>
  ∃ P : CochainComplex X.Modules ℤ, perfectSupported T.ι P ∧
    Nonempty (DerivedCategory.Q.obj ((R).obj P) ≅ DerivedCategory.Q.obj E)

/-- The same image property on actual derived objects. -/
def derivedObjects : ObjectProperty (DerivedCategory U.Modules) := fun E =>
  ∃ P : CochainComplex X.Modules ℤ, perfectSupported T.ι P ∧
    Nonempty (DerivedCategory.Q.obj ((R).obj P) ≅ E)

@[simp] theorem derivedObjects_Q_obj_iff (E : CochainComplex U.Modules ℤ) :
    derivedObjects j T (DerivedCategory.Q.obj E) ↔ complexObjects j T E := Iff.rfl

/-- Membership is invariant under an actual isomorphism of the derived objects. -/
theorem complexObjects_iff_of_derivedIso {E E' : CochainComplex U.Modules ℤ}
    (e : DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj E') :
    complexObjects j T E ↔ complexObjects j T E' := by
  constructor
  · rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩
  · rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e.symm⟩⟩

/-- Both directions of weak repleteness use the unchanged chain map. -/
theorem complexObjects_iff_of_quasiIso {E E' : CochainComplex U.Modules ℤ}
    (f : E ⟶ E') [QuasiIso f] : complexObjects j T E ↔ complexObjects j T E' :=
  complexObjects_iff_of_derivedIso j T (asIso (DerivedCategory.Q.map f))

/-- Membership implies native perfectness, for the original complex. -/
theorem perfectSupported_of_mem {E : CochainComplex U.Modules ℤ}
    (hE : complexObjects j T E) : perfectSupported (j ⁻¹ᵁ T).ι E := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  exact (perfectSupported_iff_of_derivedIso (j ⁻¹ᵁ T).ι e).1
    (perfectSupported_restrict j T hP)

/-- The full category has exactly one wrapper around each original chain complex. -/
abbrev Obj := (complexObjects j T).FullSubcategory

/-- The actual inclusion into native supported perfect complexes retains all chain maps. -/
def inclusion : Obj j T ⥤
    ObjectProperty.FullSubcategory (perfectSupported (j ⁻¹ᵁ T).ι) :=
  ObjectProperty.ιOfLE (fun _ h => perfectSupported_of_mem j T h)

/-- Restriction corestricts to its honest image using the reflexive derived witness. -/
def corestrict :
    ObjectProperty.FullSubcategory (perfectSupported T.ι) ⥤
      Obj j T :=
  (complexObjects j T).lift
    (ObjectProperty.ι (perfectSupported T.ι) ⋙ R)
    (fun P => ⟨P.obj, P.property, ⟨Iso.refl _⟩⟩)

@[simp] theorem corestrict_obj
    (P : ObjectProperty.FullSubcategory (perfectSupported T.ι)) :
    ((corestrict j T).obj P).obj = (R).obj P.obj := rfl

@[simp] theorem corestrict_map
    {P Q : ObjectProperty.FullSubcategory (perfectSupported T.ι)}
    (f : P ⟶ Q) : ((corestrict j T).map f).hom = (R).map f.hom := rfl

/-- Composition with the full inclusion is the original native restriction functor. -/
@[simp] theorem corestrict_comp_inclusion :
    corestrict j T ⋙ inclusion j T = perfectSupportedRestrict j T := rfl

/-- Every membership witness supplies a cospan of actual quasi-isomorphisms. -/
theorem exists_weak_cospan {E : CochainComplex U.Modules ℤ} (hE : complexObjects j T E) :
    ∃ (P : CochainComplex X.Modules ℤ) (M : CochainComplex U.Modules ℤ)
      (p : (R).obj P ⟶ M) (s : E ⟶ M),
      perfectSupported T.ι P ∧
      perfectSupported (j ⁻¹ᵁ T).ι M ∧ QuasiIso p ∧ QuasiIso s := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  obtain ⟨M, p, s, hs', hfac⟩ := DerivedCategory.left_fac e.hom
  have hs : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs'
  have he : e.hom ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map p := by
    let := hs'
    rw [hfac, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hp : IsIso (DerivedCategory.Q.map p) := by rw [← he]; infer_instance
  exact ⟨P, M, p, s, hP,
    (perfectSupported_iff_of_quasiIso (j ⁻¹ᵁ T).ι s).1
      (perfectSupported_of_mem j T ⟨P, hP, ⟨e⟩⟩),
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).1 hp, hs⟩

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

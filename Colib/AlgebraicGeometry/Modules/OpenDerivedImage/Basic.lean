/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOpenRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# The derived-saturated image of open restriction

An actual complex belongs to this full subcategory if its derived object is isomorphic to the
restriction of a native Stacks perfect complex. This definition preserves every original chain
map and does not assert that every perfect complex on the open extends globally.

Adapted from Quillen's `OpenDerivedImage/Basic.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, with native Mathlib and Stacks objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules]

local notation "R" => Functor.mapHomologicalComplex (restrictFunctor j) (ComplexShape.up ℤ)

/-- Actual complexes derived-isomorphic to restrictions of native perfect complexes. -/
def complexObjects : ObjectProperty (CochainComplex U.Modules ℤ) := fun E =>
  ∃ P : CochainComplex X.Modules ℤ, RingedSpace.IsPerfectComplex (X := X.toRingedSpace) P ∧
    Nonempty (DerivedCategory.Q.obj ((R).obj P) ≅ DerivedCategory.Q.obj E)

/-- The same image property on actual derived objects. -/
def derivedObjects : ObjectProperty (DerivedCategory U.Modules) := fun E =>
  ∃ P : CochainComplex X.Modules ℤ, RingedSpace.IsPerfectComplex (X := X.toRingedSpace) P ∧
    Nonempty (DerivedCategory.Q.obj ((R).obj P) ≅ E)

@[simp] theorem derivedObjects_Q_obj_iff (E : CochainComplex U.Modules ℤ) :
    derivedObjects j (DerivedCategory.Q.obj E) ↔ complexObjects j E := Iff.rfl

/-- Membership is invariant under an actual isomorphism of the derived objects. -/
theorem complexObjects_iff_of_derivedIso {E E' : CochainComplex U.Modules ℤ}
    (e : DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj E') :
    complexObjects j E ↔ complexObjects j E' := by
  constructor
  · rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩
  · rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e.symm⟩⟩

/-- Both directions of weak repleteness use the unchanged chain map. -/
theorem complexObjects_iff_of_quasiIso {E E' : CochainComplex U.Modules ℤ}
    (f : E ⟶ E') [QuasiIso f] : complexObjects j E ↔ complexObjects j E' :=
  complexObjects_iff_of_derivedIso j (asIso (DerivedCategory.Q.map f))

/-- Membership implies native perfectness, for the original complex. -/
theorem isPerfectComplex_of_mem {E : CochainComplex U.Modules ℤ}
    (hE : complexObjects j E) : RingedSpace.IsPerfectComplex (X := U.toRingedSpace) E := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  have hr : CochainComplex.QuasiIsoRoof ((R).obj P) E :=
    (CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).2 ⟨e⟩
  exact (RingedSpace.isPerfectComplex_iff_of_quasiIsoRoof hr).1
    (Complex.isPerfectComplex_restrictOpenImmersion j P hP)

/-- The full category has exactly one wrapper around each original chain complex. -/
abbrev Obj := (complexObjects j).FullSubcategory

/-- The actual inclusion into native perfect complexes retains all chain maps. -/
def inclusion : Obj j ⥤
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := U.toRingedSpace)) :=
  ObjectProperty.ιOfLE (fun _ h => isPerfectComplex_of_mem j h)

/-- Restriction corestricts to its honest image using the reflexive derived witness. -/
def corestrict :
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) ⥤
      Obj j :=
  (complexObjects j).lift
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) ⋙ R)
    (fun P => ⟨P.obj, P.property, ⟨Iso.refl _⟩⟩)

@[simp] theorem corestrict_obj
    (P : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    ((corestrict j).obj P).obj = (R).obj P.obj := rfl

@[simp] theorem corestrict_map
    {P Q : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (f : P ⟶ Q) : ((corestrict j).map f).hom = (R).map f.hom := rfl

/-- Composition with the full inclusion is the original native restriction functor. -/
@[simp] theorem corestrict_comp_inclusion :
    corestrict j ⋙ inclusion j = perfectComplexesRestrictOpenImmersion j := rfl

/-- Every membership witness supplies a cospan of actual quasi-isomorphisms. -/
theorem exists_weak_cospan {E : CochainComplex U.Modules ℤ} (hE : complexObjects j E) :
    ∃ (P : CochainComplex X.Modules ℤ) (M : CochainComplex U.Modules ℤ)
      (p : (R).obj P ⟶ M) (s : E ⟶ M),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) P ∧
      RingedSpace.IsPerfectComplex (X := U.toRingedSpace) M ∧ QuasiIso p ∧ QuasiIso s := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  obtain ⟨M, p, s, hs', hfac⟩ := DerivedCategory.left_fac e.hom
  have hs : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs'
  have he : e.hom ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map p := by
    let := hs'
    rw [hfac, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hp : IsIso (DerivedCategory.Q.map p) := by rw [← he]; infer_instance
  exact ⟨P, M, p, s, hP,
    (isPerfectComplex_of_mem j ⟨P, hP, ⟨e⟩⟩).of_quasiIso s hs,
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).1 hp, hs⟩

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

attribute [colib_tag "COL-0312",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/OpenDerivedImage/Basic.lean"
    "adaptation"
    "The honest image uses native Stacks perfect complexes and retains original chain maps"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.complexObjects
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.derivedObjects
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.isPerfectComplex_of_mem
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.corestrict
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.exists_weak_cospan

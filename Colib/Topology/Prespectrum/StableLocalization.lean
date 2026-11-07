/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.StableEquivalence
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Localization.Construction

/-!
The actual coherent-homotopy quotient and categorical stable localization, with original
stable-group functors and a proved universal lift. No stable model structure or triangulation is
asserted.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StableLocalization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native `Topology.LoopPrespectrum`, full coherent based homotopies, all integer
stable groups and Mathlib's actual quotient and localization constructions are retained.
The universal target has independent object and morphism universes. -/
@[expose] public section


noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- Original coherent based homotopies are the generating relation. -/
def coherentHomotopyRelation : HomRel LoopPrespectrum.{u} :=
  fun _ _ f g ↦ Nonempty (Homotopy f g)

/-- The actual category quotient by full coherent based homotopies. -/
abbrev CoherentHomotopyCategory := CategoryTheory.Quotient coherentHomotopyRelation.{u}

/-- The quotient functor identifying maps joined by a coherent prespectrum homotopy. -/
def coherentHomotopyQuotient : LoopPrespectrum.{u} ⥤ CoherentHomotopyCategory.{u} :=
  CategoryTheory.Quotient.functor _

theorem coherentHomotopyQuotient_map_eq {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (H : Homotopy f g) :
    coherentHomotopyQuotient.map f = coherentHomotopyQuotient.map g :=
  CategoryTheory.Quotient.sound _ ⟨H⟩

/-- Actual integer stable groups descend through the whole-homotopy quotient. -/
def coherentStableHomotopyFunctor (d : ℤ) :
    CoherentHomotopyCategory.{u} ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.Quotient.lift _ (stableHomotopyFunctor d)
    (fun _ _ _ _ ⟨H⟩ ↦ H.stableHomotopyMap_eq d)

@[simp] theorem coherentStableHomotopyFunctor_original_map (d : ℤ)
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    (coherentStableHomotopyFunctor d).map (coherentHomotopyQuotient.map f) =
      (stableHomotopyFunctor d).map f := rfl

/-- The original all-integer stable equivalence condition on actual quotient maps. -/
def coherentStableEquivalences : MorphismProperty CoherentHomotopyCategory.{u} :=
  fun _ _ f ↦ ∀ d : ℤ, IsIso ((coherentStableHomotopyFunctor d).map f)

@[simp] theorem coherentStableEquivalences_original_iff
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    coherentStableEquivalences (coherentHomotopyQuotient.map f) ↔ IsStableEquivalence f := Iff.rfl

/-- A constructed categorical localization of original prespectra after their
coherent homotopies. No stable model structure or triangulation is assumed. -/
abbrev StableLocalization := coherentStableEquivalences.{u}.Localization

/-- The functor to the localization at the stable equivalences. -/
def toStableLocalization : LoopPrespectrum.{u} ⥤ StableLocalization.{u} :=
  coherentHomotopyQuotient ⋙ coherentStableEquivalences.Q

/-- The genuine localization retains every original stable group functor. -/
def localizedStableHomotopyFunctor (d : ℤ) : StableLocalization.{u} ⥤ AddCommGrpCat.{u} :=
  Localization.Construction.lift (coherentStableHomotopyFunctor d) (fun _ _ _ hf ↦ hf d)

@[simp] theorem localizedStableHomotopyFunctor_original_obj (d : ℤ) (E : LoopPrespectrum.{u}) :
    (localizedStableHomotopyFunctor d).obj (toStableLocalization.obj E) = stableHomotopyGroup E d :=
      rfl

@[simp] theorem localizedStableHomotopyFunctor_original_map (d : ℤ)
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    (localizedStableHomotopyFunctor d).map (toStableLocalization.map f) =
      (stableHomotopyFunctor d).map f := rfl

/-- The inverse of an actual stable equivalence is a genuine morphism in the
constructed localization, with both inverse identities. -/
def stableLocalizationIso {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : IsStableEquivalence f) : toStableLocalization.obj E ≅ toStableLocalization.obj F :=
  Localization.Construction.wIso (coherentHomotopyQuotient.map f) hf

@[simp] theorem stableLocalizationIso_hom {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : IsStableEquivalence f) : (stableLocalizationIso f hf).hom = toStableLocalization.map f :=
      rfl

/-- An original map becomes invertible exactly when all its actual stable maps
are invertible; the converse is detected by the descended original functors. -/
theorem toStableLocalization_isIso_iff {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    IsIso (toStableLocalization.map f) ↔ IsStableEquivalence f := by
  constructor
  · intro h d
    let := h
    change IsIso ((localizedStableHomotopyFunctor d).map (toStableLocalization.map f))
    infer_instance
  · intro h
    exact (stableLocalizationIso f h).isIso_hom

/-- Actual full coherent homotopies become equal arrows, before any choice of inverse. -/
theorem toStableLocalization_map_eq_of_homotopy {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (H : Homotopy f g) :
    toStableLocalization.map f = toStableLocalization.map g :=
  congrArg coherentStableEquivalences.Q.map (coherentHomotopyQuotient_map_eq H)

universe v w
variable {D : Type v} [Category.{w} D] (T : LoopPrespectrum.{u} ⥤ D)
  (hH : ∀ {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}, Homotopy f g → T.map f = T.map g)
  (hW : ∀ {E F : LoopPrespectrum.{u}} (f : E ⟶ F), IsStableEquivalence f → IsIso (T.map f))

/-- The lift of the given homotopy-invariant functor through the coherent homotopy category. -/
def stableLocalizationHomotopyLift : CoherentHomotopyCategory.{u} ⥤ D :=
  CategoryTheory.Quotient.lift _ T (fun _ _ _ _ ⟨H⟩ ↦ hH H)

include hW in
lemma stableLocalizationHomotopyLift_inverts :
    coherentStableEquivalences.IsInvertedBy (stableLocalizationHomotopyLift T hH) := by
  intro E F f hf
  induction f using CategoryTheory.Quotient.induction with
  | h f => exact hW f hf

/-- The actual universal lift for a functor respecting whole homotopies and
inverting every original stable equivalence. -/
def stableLocalizationLift : StableLocalization.{u} ⥤ D :=
  Localization.Construction.lift (stableLocalizationHomotopyLift T hH)
    (stableLocalizationHomotopyLift_inverts T hH hW)

@[simp] theorem toStableLocalization_comp_lift :
    toStableLocalization ⋙ stableLocalizationLift T hH hW = T := by
  change (coherentHomotopyQuotient ⋙ coherentStableEquivalences.Q) ⋙ _ = _
  rw [Functor.assoc]
  unfold stableLocalizationLift
  rw [Localization.Construction.fac]
  exact CategoryTheory.Quotient.lift_spec _ _ _

/-- Strict uniqueness of the constructed universal lift. -/
theorem stableLocalizationLift_unique (L : StableLocalization.{u} ⥤ D)
    (hL : toStableLocalization ⋙ L = T) : L = stableLocalizationLift T hH hW := by
  apply Localization.Construction.uniq
  apply CategoryTheory.Quotient.lift_unique'
  change toStableLocalization ⋙ L = toStableLocalization ⋙ stableLocalizationLift T hH hW
  rw [hL, toStableLocalization_comp_lift]

attribute [colib_tag "COL-0292"] stableLocalizationLift
  toStableLocalization_comp_lift stableLocalizationLift_unique toStableLocalization_isIso_iff

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/Quotient.lean: lift, lift_spec, lift_unique'"
  "ingredient" "The actual congruence quotient by whole coherent homotopies and its strict descent",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/CategoryTheory/Localization/Construction.lean: lift, fac, uniq"
    "ingredient" "The existing categorical localization of an arbitrary morphism property,
      with actual formal inverses and strict universal factorization"]
  stableLocalizationLift stableLocalizationLift_unique

end Topology.LoopPrespectrum

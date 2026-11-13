/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveResolution

/-!
# The projective model of the bounded-above transfer derived category

The native derived quotient is fully faithful on bounded-above complexes
of projective transfer presheaves. The proved projective resolution theorem
supplies its essential surjectivity. Applying an additive functor to these
representatives gives its projective realization on the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "c" => ComplexShape.up ℤ

/-- Bounded-above complexes whose original terms are projective. -/
def boundedAboveProjectiveCondition :
    ObjectProperty (HomotopyCategory (PresheafWithTransfers.{u + 1} k) c) :=
  fun K =>
    let E : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ := K.as
    ∃ n : ℤ, E.IsStrictlyLE n ∧ ∀ i : ℤ, Projective (E.X i)

/-- The native homotopy category on bounded-above projective complexes. -/
abbrev BoundedAboveProjectiveHomotopy := (boundedAboveProjectiveCondition k).FullSubcategory

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

/-- The derived quotient restricted to the original projective complexes. -/
def projectiveHomotopyToDerivedMinus :
    BoundedAboveProjectiveHomotopy k ⥤
      DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) :=
  (DerivedCategory.TStructure.t (C := PresheafWithTransfers.{u + 1} k)).minus.lift
    ((boundedAboveProjectiveCondition k).ι ⋙ DerivedCategory.Qh) (fun K => by
      obtain ⟨n, hn, _⟩ := K.property
      let E : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ := K.obj.as
      let : E.IsStrictlyLE n := hn
      let : (DerivedCategory.Q.obj E).IsLE n := inferInstance
      exact ⟨n, DerivedCategory.TStructure.t.isLE_of_iso
        ((DerivedCategory.quotientCompQhIso _).app E).symm n⟩)

private theorem projectiveHomotopyToDerivedMinus_map_bijective
    (K L : BoundedAboveProjectiveHomotopy k) :
    Function.Bijective ((projectiveHomotopyToDerivedMinus k).map :
      (K ⟶ L) → _) := by
  obtain ⟨n, hn, hP⟩ := K.property
  let E : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ := K.obj.as
  let : E.IsStrictlyLE n := hn
  let : ∀ i : ℤ, Projective (E.X i) := hP
  let : E.IsKProjective := CochainComplex.isKProjective_of_projective E n
  have h : Function.Bijective (DerivedCategory.Qh.map :
      (K.obj ⟶ L.obj) → _) := CochainComplex.IsKProjective.Qh_map_bijective E L.obj
  constructor
  · intro f g hfg
    apply ObjectProperty.hom_ext
    exact h.1 (congrArg (fun z => z.hom) hfg)
  · intro f
    obtain ⟨g, hg⟩ := h.2 f.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg

instance : (projectiveHomotopyToDerivedMinus k).Full where
  map_surjective := (projectiveHomotopyToDerivedMinus_map_bijective k _ _).2

instance : (projectiveHomotopyToDerivedMinus k).Faithful where
  map_injective {X Y} {_ _} h := (projectiveHomotopyToDerivedMinus_map_bijective k X Y).1 h

instance : (projectiveHomotopyToDerivedMinus k).EssSurj where
  mem_essImage K := by
    obtain ⟨P, n, hP, hproj, _, ⟨e⟩⟩ := exists_projectiveRepresentative K
    refine ⟨⟨(HomotopyCategory.quotient _ c).obj P, ⟨n, hP, hproj⟩⟩, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso _).app P ≪≫ e)

instance : (projectiveHomotopyToDerivedMinus k).IsEquivalence where

/-- The original quotient identifies the projective model with the derived category. -/
def boundedAboveProjectiveEquivalence :
    BoundedAboveProjectiveHomotopy k ≌
      DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) :=
  (projectiveHomotopyToDerivedMinus k).asEquivalence

/-- The functor on projective complexes obtained by applying an additive coefficient functor. -/
def projectiveHomotopyMapToDerivedMinus
    (F : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k) [F.Additive] :
    BoundedAboveProjectiveHomotopy k ⥤
      DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) :=
  (DerivedCategory.TStructure.t (C := PresheafWithTransfers.{u + 1} k)).minus.lift
    ((boundedAboveProjectiveCondition k).ι ⋙ F.mapHomotopyCategory c ⋙ DerivedCategory.Qh)
    (fun K => by
      obtain ⟨n, hn, _⟩ := K.property
      let E : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ := K.obj.as
      let : E.IsStrictlyLE n := hn
      let L : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ :=
        (F.mapHomologicalComplex c).obj E
      let : L.IsStrictlyLE n := (CochainComplex.isStrictlyLE_iff L n).2
        (fun i hi => F.map_isZero (E.isZero_of_isStrictlyLE n i hi))
      let : (DerivedCategory.Q.obj L).IsLE n := inferInstance
      exact ⟨n, DerivedCategory.TStructure.t.isLE_of_iso
        ((DerivedCategory.quotientCompQhIso _).app L).symm n⟩)

/-- Apply the coefficient functor to bounded-above projective representatives. -/
def projectiveDerivedMinusFunctor
    (F : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k) [F.Additive] :
    DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) :=
  (boundedAboveProjectiveEquivalence k).inverse ⋙ projectiveHomotopyMapToDerivedMinus k F

end AlgebraicGeometry.PresheafWithTransfers

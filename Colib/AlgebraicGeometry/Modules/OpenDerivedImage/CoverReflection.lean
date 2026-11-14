/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.TwoOpenLocality
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedPushforward
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.TwoOpens

/-! # Reflection of the derived image of restriction across two opens

A perfect complex on one member of a two-open cover extends to the ambient
scheme if and only if its restriction to the intersection extends to the other
member. The gluing uses an actual isomorphism on the intersection
([Stacks, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)); no quasi-isomorphism
of chosen representatives is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
open Stacks.Cohomology.GlueingComplexes (exists_glueing overlapIso)
open Stacks.SchemeCohomology (hom)

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens)

local notation "U" => Scheme.Opens.toScheme T
local notation "jbase" => PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j))
local notation "I₀" => Functor.obj (TopologicalSpace.Opens.map jbase) T
local notation "W" => Scheme.Opens.toScheme I₀
local notation "i" => Scheme.Opens.ι T
local notation "b" => Scheme.Opens.ι I₀
local notation "a" => Scheme.Hom.resLE j T I₀ le_rfl
local notation "F" f => CategoryTheory.Functor.mapDerivedCategory (restrictFunctor f)
local notation "R" f => CategoryTheory.Functor.mapHomologicalComplex
  (restrictFunctor f) (ComplexShape.up ℤ)

local instance : IsOpenImmersion a := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

omit [IsOpenImmersion j] in
/-- The ringed-space square of the two open immersions and their intersection is Cartesian. -/
theorem coverReflection_isPullback :
    IsPullback (hom a) (hom b) (hom i) (hom j) := by
  have hs : a ≫ i = b ≫ j := j.resLE_comp_ι le_rfl
  have hcomm : hom a ≫ hom i = hom b ≫ hom j := by
    simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
      congrArg (fun k : W ⟶ X => k.toLRSHom.toShHom) hs
  refine Stacks.DerivedQCoh.isPullback_of_range _ _ _ _ hcomm fun z hz => ?_
  obtain ⟨y, hy⟩ := hz
  have hy' : y.val = j.base z := hy
  have hz' : j.base z ∈ T := hy' ▸ y.property
  exact ⟨⟨z, hz'⟩, rfl⟩

/-- The exact restrictions on the derived category agree on the actual intersection. -/
def coverReflectionRestrictionIso : (F i) ⋙ (F a) ≅ (F j) ⋙ (F b) :=
  Functor.isoWhiskerRight (derivedRestrictIsoDerivedPullback i) _ ≪≫
    Functor.isoWhiskerLeft _ (derivedRestrictIsoDerivedPullback a) ≪≫
    overlapIso (hom i) (hom j) (hom a) (hom b)
      (IsPullback.toCommSq (coverReflection_isPullback j T)).w ≪≫
    Functor.isoWhiskerLeft _ (derivedRestrictIsoDerivedPullback b).symm ≪≫
    Functor.isoWhiskerRight (derivedRestrictIsoDerivedPullback j).symm _

set_option maxHeartbeats 500000 in
-- The actual gluing comparison identifies the scheme and ringed-space spellings.
/-- Membership in the derived image of open restriction is reflected on the intersection. -/
theorem complexObjects_cover_iff
    (hcover : ∀ x : X, x ∈ Set.range j.base ∨ x ∈ T)
    (E : CochainComplex (U).Modules ℤ)
    (hE : RingedSpace.IsPerfectComplex (X := (U).toRingedSpace) E) :
    complexObjects i E ↔ complexObjects b ((R a).obj E) := by
  constructor
  · rintro ⟨P, hP, ⟨e⟩⟩
    let f := (restrictFunctor i).mapDerivedCategoryFactors.app P
    let g := (restrictFunctor j).mapDerivedCategoryFactors.app P
    let ea := (restrictFunctor a).mapDerivedCategoryFactors
    let eb := (restrictFunctor b).mapDerivedCategoryFactors
    refine ⟨(R j).obj P, Complex.isPerfectComplex_restrictOpenImmersion j P hP, ⟨?_⟩⟩
    exact (eb.app ((R j).obj P)).symm ≪≫ (F b).mapIso g.symm ≪≫
      ((coverReflectionRestrictionIso j T).app (DerivedCategory.Q.obj P)).symm ≪≫
      (F a).mapIso (f ≪≫ e) ≪≫ ea.app E
  · rintro ⟨B, hB, ⟨e⟩⟩
    let A₀ := DerivedCategory.Q.obj E
    let B₀ := DerivedCategory.Q.obj B
    let ea := (restrictFunctor a).mapDerivedCategoryFactors.app E
    let eb := (restrictFunctor b).mapDerivedCategoryFactors.app B
    let c := ((derivedRestrictIsoDerivedPullback a).app A₀).symm ≪≫ ea ≪≫ e.symm ≪≫
      eb.symm ≪≫ (derivedRestrictIsoDerivedPullback b).app B₀
    obtain ⟨G⟩ := exists_glueing (hom i) (hom j) (hom a) (hom b)
      (coverReflection_isPullback j T) A₀ B₀ c
    let eU := (derivedRestrictIsoDerivedPullback i).app G.F ≪≫ G.f
    let eV := (derivedRestrictIsoDerivedPullback j).app G.F ≪≫ G.g
    have hcover' : ∀ x : X, x ∈ Set.range (i).base ∨ x ∈ Set.range j.base := by
      intro x
      exact (hcover x).symm.imp (fun hx => ⟨⟨x, hx⟩, rfl⟩) id
    have hU : Stacks.Cohomology.PerfectComplexes.IsPerfect
        (X := (U).toRingedSpace) ((F i).obj G.F) := ⟨E, hE, ⟨eU.symm⟩⟩
    have hV : Stacks.Cohomology.PerfectComplexes.IsPerfect
        (X := V.toRingedSpace) ((F j).obj G.F) := ⟨B, hB, ⟨eV.symm⟩⟩
    have hG := Stacks.DerivedQCoh.isPerfect_of_cover i j hcover' G.F hU hV
    obtain ⟨P, hP, ⟨ep⟩⟩ := hG
    exact ⟨P, hP, ⟨((restrictFunctor i).mapDerivedCategoryFactors.app P).symm ≪≫
      (F i).mapIso ep ≪≫ eU⟩⟩

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/\
    OpenDerivedImage/CoverReflection.lean:46-86"
  "adaptation" "Reflection of the derived restriction image across two opens"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.complexObjects_cover_iff

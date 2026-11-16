/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.CoverReflection

/-! # Simultaneous restriction of a glued native perfect complex -/

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
local notation:max "F[" f "]" => CategoryTheory.Functor.mapDerivedCategory (restrictFunctor f)
local notation:max "R[" f "]" => CategoryTheory.Functor.mapHomologicalComplex
  (restrictFunctor f) (ComplexShape.up ℤ)

local instance twoOpenGlueOverlapOpen : IsOpenImmersion a := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

set_option maxHeartbeats 500000 in
-- The native module and ringed-space restriction functors have different presentations.
/-- An actual derived overlap isomorphism glues the two perfect complexes, with both
original restriction isomorphisms retained. -/
theorem exists_perfect_of_overlap_iso
    (hcover : ∀ x : X, x ∈ Set.range j.base ∨ x ∈ T)
    (E : CochainComplex (U).Modules ℤ) (B : CochainComplex V.Modules ℤ)
    (hE : RingedSpace.IsPerfectComplex (X := (U).toRingedSpace) E)
    (hB : RingedSpace.IsPerfectComplex (X := V.toRingedSpace) B)
    (e : DerivedCategory.Q.obj (R[b].obj B) ≅ DerivedCategory.Q.obj (R[a].obj E)) :
    ∃ P : CochainComplex X.Modules ℤ, RingedSpace.IsPerfectComplex (X := X.toRingedSpace) P ∧
      Nonempty (DerivedCategory.Q.obj (R[i].obj P) ≅ DerivedCategory.Q.obj E) ∧
      Nonempty (DerivedCategory.Q.obj (R[j].obj P) ≅ DerivedCategory.Q.obj B) := by
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
      (X := (U).toRingedSpace) (F[i].obj G.F) := ⟨E, hE, ⟨eU.symm⟩⟩
  have hV : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := V.toRingedSpace) (F[j].obj G.F) := ⟨B, hB, ⟨eV.symm⟩⟩
  have hG := Stacks.DerivedQCoh.isPerfect_of_cover i j hcover' G.F hU hV
  obtain ⟨P, hP, ⟨ep⟩⟩ := hG
  exact ⟨P, hP, ⟨((restrictFunctor i).mapDerivedCategoryFactors.app P).symm ≪≫
    F[i].mapIso ep ≪≫ eU⟩, ⟨((restrictFunctor j).mapDerivedCategoryFactors.app P).symm ≪≫
    F[j].mapIso ep ≪≫ eV⟩⟩

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

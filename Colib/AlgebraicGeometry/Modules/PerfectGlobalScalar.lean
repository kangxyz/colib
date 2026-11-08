/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOpenRestriction
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishingAffine

/-! # Global scalars and units on native perfect complexes

The sheaf action is the existing `Stacks.RegularSequence.globalSmulCenter`. We only
lift its components to chain maps and the native full subcategory. Restriction uses the
existing `globalSmulCenter_restrict`; no alternative sheaf scalar action is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.RegularSequence (globalSmulCenter globalSmulCenter_app_app)

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable (X : Scheme.{u})

/-- Multiplication by an actual global section, degree by degree. -/
def complexGlobalScalar (r : Γ(X, ⊤)) :
    𝟭 (CochainComplex X.Modules ℤ) ⟶ 𝟭 (CochainComplex X.Modules ℤ) where
  app K :=
    { f n := (globalSmulCenter X r).app (K.X n)
      comm' i j _ := ((globalSmulCenter X r).naturality (K.d i j)).symm }
  naturality {K L} f := by
    ext n : 1
    exact (globalSmulCenter X r).naturality (f.f n)

@[simp] theorem complexGlobalScalar_app_f (r : Γ(X, ⊤))
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((complexGlobalScalar X r).app K).f n = (globalSmulCenter X r).app (K.X n) := rfl

/-- The scalar one acts as the actual identity chain map. -/
@[simp] theorem complexGlobalScalar_one : complexGlobalScalar X 1 = 𝟙 _ := by
  ext K n U m
  simp [complexGlobalScalar, globalSmulCenter_app_app]

/-- Composition of actual scalar chain maps is multiplication of their sections. -/
theorem complexGlobalScalar_mul (r s : Γ(X, ⊤)) :
    complexGlobalScalar X (r * s) = complexGlobalScalar X r ≫ complexGlobalScalar X s := by
  ext K n U m
  simp [complexGlobalScalar, globalSmulCenter_app_app, mul_smul]

/-- The scalar natural transformation on the native full subcategory of perfect complexes. -/
def perfectGlobalScalar (r : Γ(X, ⊤)) :
    𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) ⟶
      𝟭 (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) where
  app K := ObjectProperty.homMk ((complexGlobalScalar X r).app K.obj)
  naturality {K L} f := by
    apply ObjectProperty.hom_ext
    exact (complexGlobalScalar X r).naturality f.hom

@[simp] theorem perfectGlobalScalar_app_hom (r : Γ(X, ⊤))
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    ((perfectGlobalScalar X r).app K).hom = (complexGlobalScalar X r).app K.obj := rfl

@[simp] theorem perfectGlobalScalar_one : perfectGlobalScalar X 1 = 𝟙 _ := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun t => t.app K.obj) (complexGlobalScalar_one X)

theorem perfectGlobalScalar_mul (r s : Γ(X, ⊤)) :
    perfectGlobalScalar X (r * s) = perfectGlobalScalar X r ≫ perfectGlobalScalar X s := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun t => t.app K.obj) (complexGlobalScalar_mul X r s)

/-- A global unit acts by the scalar itself, with the actual inverse scalar as inverse. -/
def complexGlobalUnitIso (q : (Γ(X, ⊤))ˣ) :
    𝟭 (CochainComplex X.Modules ℤ) ≅ 𝟭 (CochainComplex X.Modules ℤ) where
  hom := complexGlobalScalar X (q : Γ(X, ⊤))
  inv := complexGlobalScalar X (↑(q⁻¹) : Γ(X, ⊤))
  hom_inv_id := by rw [← complexGlobalScalar_mul]; simp
  inv_hom_id := by rw [← complexGlobalScalar_mul]; simp

/-- The global unit natural isomorphism on the actual native perfect category. -/
def perfectGlobalUnitIso (q : (Γ(X, ⊤))ˣ) :
    𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) ≅
      𝟭 (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) where
  hom := perfectGlobalScalar X (q : Γ(X, ⊤))
  inv := perfectGlobalScalar X (↑(q⁻¹) : Γ(X, ⊤))
  hom_inv_id := by rw [← perfectGlobalScalar_mul]; simp
  inv_hom_id := by rw [← perfectGlobalScalar_mul]; simp

@[simp] theorem perfectGlobalUnitIso_hom_app_hom_f (q : (Γ(X, ⊤))ˣ)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    (n : ℤ) :
    (((perfectGlobalUnitIso X q).hom.app K).hom).f n =
      (globalSmulCenter X (q : Γ(X, ⊤))).app (K.obj.X n) := rfl

@[simp] theorem perfectGlobalUnitIso_inv_app_hom_f (q : (Γ(X, ⊤))ˣ)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    (n : ℤ) :
    (((perfectGlobalUnitIso X q).inv.app K).hom).f n =
      (globalSmulCenter X (↑(q⁻¹) : Γ(X, ⊤))).app (K.obj.X n) := rfl

variable {X} {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- Literal restriction commutes with multiplication by the pulled-back global section. -/
theorem restrict_map_complexGlobalScalar (r : Γ(X, ⊤)) (K : CochainComplex X.Modules ℤ) :
    ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((complexGlobalScalar X r).app K) =
    (complexGlobalScalar Y (j.appTop r)).app
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  ext n : 1
  exact Stacks.RegularSequence.globalSmulCenter_restrict j (K.X n) r

/-- The same equality inside the actual perfect full subcategory. -/
theorem perfectRestrict_map_globalScalar (r : Γ(X, ⊤))
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectComplexesRestrictOpenImmersion j).map ((perfectGlobalScalar X r).app K) =
      (perfectGlobalScalar Y (j.appTop r)).app
        ((perfectComplexesRestrictOpenImmersion j).obj K) := by
  apply ObjectProperty.hom_ext
  exact restrict_map_complexGlobalScalar j r K.obj

/-- A scalar restricting to the specified unit is the actual unit arrow after restriction. -/
theorem perfectRestrict_scalar_eq_globalUnit (r : Γ(X, ⊤)) (q : (Γ(Y, ⊤))ˣ)
    (hq : j.appTop r = ↑q)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectComplexesRestrictOpenImmersion j).map ((perfectGlobalScalar X r).app K) =
      (perfectGlobalUnitIso Y q).hom.app
        ((perfectComplexesRestrictOpenImmersion j).obj K) := by
  rw [perfectRestrict_map_globalScalar, hq]
  rfl

/-- Restriction of this actual scalar arrow is an isomorphism in the perfect category. -/
theorem isIso_perfectRestrict_scalar (r : Γ(X, ⊤)) (q : (Γ(Y, ⊤))ˣ)
    (hq : j.appTop r = ↑q)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    IsIso ((perfectComplexesRestrictOpenImmersion j).map ((perfectGlobalScalar X r).app K)) := by
  rw [perfectRestrict_scalar_eq_globalUnit j r q hq K]
  infer_instance

/-- On ambient complexes the restricted scalar is genuinely a quasi-isomorphism. -/
theorem quasiIso_restrict_complexGlobalScalar (r : Γ(X, ⊤)) (q : (Γ(Y, ⊤))ˣ)
    (hq : j.appTop r = ↑q) (K : CochainComplex X.Modules ℤ) :
    QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((complexGlobalScalar X r).app K)) := by
  rw [restrict_map_complexGlobalScalar, hq]
  change QuasiIso ((complexGlobalUnitIso Y q).hom.app _)
  infer_instance

end AlgebraicGeometry.Scheme.Modules

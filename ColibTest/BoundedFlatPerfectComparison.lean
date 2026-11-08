/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectComparison

/-!
# Full-Signature Relative Flat Comparison Consumers

Actual chain maps, explicit b+1 bounds, genuine quasi-isomorphisms, admissible flat perfect
quotients and the strict triangle are retained. The scheme specialization has only CompactSpace,
and the actual inclusion K-map and its forward equivalence are checked separately at n = 0.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect
open AlgebraicGeometry.RingedSpace

universe u v

attribute [local instance] Abelian.hasFiniteBiproducts

example {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b] :
    ∃ (M : CochainComplex C ℤ) (i : K ⟶ M) (p : M ⟶ L),
      M.IsStrictlyLE (b + 1) ∧ QuasiIso p ∧ i ≫ p = f ∧
      ∀ n, Abelian.epiWithInjectiveKernel ((i.f n).op) :=
  CochainComplex.exists_boundedAbove_relative_projective_factorization f b

example {C : Type u} [Category.{v} C] [Abelian C]
    {K M : CochainComplex C ℤ} (i : K ⟶ M)
    (hi : ∀ n, Abelian.epiWithInjectiveKernel ((i.f n).op)) (n : ℤ) :
    IsSplitMono (i.f n) ∧ Projective ((cokernel i).X n) :=
  ⟨(CochainComplex.splitMono_projective_cokernel_of_op_epiWithInjectiveKernel
      (i.f n) (hi n)).1,
    CochainComplex.relative_factorization_projective_cokernel i hi n⟩

example (X : Scheme.{u}) {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b]
    (hK : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) (K.X n)) :
    ∃ (M Q : CochainComplex X.Modules ℤ) (i : K ⟶ M) (p : M ⟶ L)
      (q : M ⟶ Q) (w : i ≫ q = 0),
      QuasiIso p ∧ i ≫ p = f ∧ (ShortComplex.mk i q w).ShortExact ∧
      M.IsStrictlyLE (b + 1) ∧ Q.IsStrictlyLE (b + 1) ∧
      (∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) (M.X n)) ∧
        ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) (Q.X n) :=
  @exists_boundedAbove_relative_flat_factorization X.toRingedSpace K L f b
    ‹K.IsStrictlyLE b› ‹L.IsStrictlyLE b› hK

example (X : Scheme.{u})
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
    (L : ObjectProperty.FullSubcategory (IsPerfectComplex (X := X.toRingedSpace)))
    (f : (boundedAboveFlatPerfectInclusion X.toRingedSpace).obj K ⟶ L) (b : ℤ)
    [K.obj.IsStrictlyLE b] [L.obj.IsLE b] :
    ∃ (M : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) (i : K ⟶ M)
      (p : (boundedAboveFlatPerfectInclusion X.toRingedSpace).obj M ⟶ L),
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof i ∧
        (perfectComplexesWaldhausen X.toRingedSpace).weq p ∧
        (boundedAboveFlatPerfectInclusion X.toRingedSpace).map i ≫ p = f :=
  boundedAboveFlatPerfect_relative_factorization_of_bound K L f b

example (X : Scheme.{u}) [CompactSpace X] :
    Waldhausen.HasApproximationProperty (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      (perfectComplexesWaldhausen X.toRingedSpace)
      (boundedAboveFlatPerfectInclusion X.toRingedSpace) :=
  boundedAboveFlatPerfectInclusion_approximation X.toRingedSpace

example (X : Scheme.{u}) [CompactSpace X]
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
    (L : ObjectProperty.FullSubcategory (IsPerfectComplex (X := X.toRingedSpace)))
    (f : (boundedAboveFlatPerfectInclusion X.toRingedSpace).obj K ⟶ L) :
    ∃ (M : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) (i : K ⟶ M)
      (p : (boundedAboveFlatPerfectInclusion X.toRingedSpace).obj M ⟶ L),
      (∃ (Q : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ)
        (_hQ : boundedAboveFlatPerfectComplex X.toRingedSpace Q)
        (q : M.obj ⟶ Q) (w : i.hom ≫ q = 0), (ShortComplex.mk i.hom q w).ShortExact) ∧
      QuasiIso p.hom ∧ (boundedAboveFlatPerfectInclusion X.toRingedSpace).map i ≫ p = f := by
  obtain ⟨M, i, p, hi, hp, hfac⟩ :=
    (boundedAboveFlatPerfectInclusion_approximation X.toRingedSpace).lift f
  exact ⟨M, i, p, (boundedAboveFlatPerfectWaldhausen_cof_iff _ i).1 hi, hp, hfac⟩

example (X : RingedSpace.{u, u}) [CompactSpace X.carrier] (n : ℕ) :
    Function.Bijective (boundedAboveFlatPerfectToPerfectKMap X n) :=
  boundedAboveFlatPerfectToPerfectKMap_bijective X n

example (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    Function.Bijective (Waldhausen.KMap
      (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace) n) :=
  boundedAboveFlatPerfectToPerfectKMap_bijective X.toRingedSpace n

example (X : Scheme.{u}) [CompactSpace X] :
    Function.Bijective (Waldhausen.KMap
      (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace) 0) :=
  boundedAboveFlatPerfectToPerfectKMap_bijective X.toRingedSpace 0

example (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    X.toRingedSpace.boundedAboveFlatPerfectK n ≃*
      (perfectComplexesWaldhausen X.toRingedSpace).K n :=
  boundedAboveFlatPerfectKEquiv X.toRingedSpace n

example (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    (↑(boundedAboveFlatPerfectKEquiv X.toRingedSpace n) :
      X.toRingedSpace.boundedAboveFlatPerfectK n →*
        (perfectComplexesWaldhausen X.toRingedSpace).K n) =
      Waldhausen.KMap (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace) n := rfl

example (X : Scheme.{u}) [CompactSpace X] :
    (↑(boundedAboveFlatPerfectKEquiv X.toRingedSpace 0) :
      X.toRingedSpace.boundedAboveFlatPerfectK 0 →*
        (perfectComplexesWaldhausen X.toRingedSpace).K 0) =
      Waldhausen.KMap (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace) 0 := rfl

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.SingularPresheafDerived
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TotalInvariance
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TotalInvariantUnit

/-!
# Fixed points of singularization on derived transfer presheaves

The original singularization has A¹-invariant cohomology. The derived unit
on an object with A¹-invariant cohomology is an isomorphism, by the bounded
cochain unit comparison and the native derived quotient.
-/

public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

/-- The actual bounded-above derived image of a cochain quasi-isomorphism is invertible. -/
theorem isIso_singularPresheafDerivedCochainMap_of_quasiIso
    {K L : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ} (f : K ⟶ L)
    (a b : ℤ) [K.IsStrictlyLE a] [L.IsStrictlyLE b] [QuasiIso f] :
    IsIso (singularPresheafDerivedCochainMap k f a b) := by
  let J : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory (PresheafWithTransfers.{u + 1} k) := DerivedCategory.Minus.ι
  let e := singularPresheafDerivedCochainToQIso k L b
  let d := singularPresheafDerivedCochainToQIso k K a
  let f' := J.map (singularPresheafDerivedCochainMap k f a b)
  have h : f' ≫ e.hom = d.hom ≫ DerivedCategory.Q.map f :=
    singularPresheafDerivedCochainToQIso_naturality k f a b
  let : IsIso (f' ≫ e.hom) := h.symm ▸ inferInstanceAs (IsIso (d.hom ≫ DerivedCategory.Q.map f))
  let : IsIso f' := IsIso.of_isIso_comp_right f' e.hom
  exact isIso_of_reflects_iso _ J

/-- Bounded-above singularization has A¹-invariant cohomology before sheafification. -/
theorem singularPresheafDerivedFunctor_cohomology_isA1Invariant
    (X : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (PresheafWithTransfers.{u + 1} k) i).obj
      ((singularPresheafDerivedFunctor k).obj X).obj).IsA1Invariant := by
  obtain ⟨b, hb⟩ := X.property
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_singularPresheafDerivedCochainObj_iso k X b hb
  let : K.IsStrictlyLE b := hK
  let C := singularTotalFunctor k
  let F := singularPresheafDerivedFunctor k
  let J : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory (PresheafWithTransfers.{u + 1} k) := DerivedCategory.Minus.ι
  let H := DerivedCategory.homologyFunctor (PresheafWithTransfers.{u + 1} k) i
  let : (C.obj K).IsStrictlyLE b := singularTotalFunctor_obj_isStrictlyLE k K b
  let d : F.obj X ≅ singularPresheafDerivedCochainObj k (C.obj K) b :=
    F.mapIso e.symm ≪≫ singularPresheafDerivedCochainIso k K b
  let a := H.mapIso (J.mapIso d ≪≫ singularPresheafDerivedCochainToQIso k (C.obj K) b) ≪≫
    (DerivedCategory.homologyFunctorFactors (PresheafWithTransfers.{u + 1} k) i).app (C.obj K)
  exact (singularTotalFunctor_homology_isA1Invariant K b i).of_iso a.symm

/-- The original augmentation is invertible on objects with A¹-invariant cohomology. -/
theorem isIso_singularPresheafDerivedUnit_app
    (X : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k))
    (hX : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (PresheafWithTransfers.{u + 1} k) i).obj
      X.obj).IsA1Invariant) :
    IsIso ((singularPresheafDerivedUnit k).app X) := by
  obtain ⟨b, hb⟩ := X.property
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_singularPresheafDerivedCochainObj_iso k X b hb
  let : K.IsStrictlyLE b := hK
  let C := singularTotalFunctor k
  let η := singularPresheafDerivedUnit k
  let J : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory (PresheafWithTransfers.{u + 1} k) := DerivedCategory.Minus.ι
  let QK := singularPresheafDerivedCochainObj k K b
  let : (C.obj K).IsStrictlyLE b := singularTotalFunctor_obj_isStrictlyLE k K b
  have h (i : ℤ) : (K.homology i).IsA1Invariant := by
    let H := DerivedCategory.homologyFunctor (PresheafWithTransfers.{u + 1} k) i
    exact (hX i).of_iso (H.mapIso (J.mapIso e.symm ≪≫ singularPresheafDerivedCochainToQIso k K b) ≪≫
      (DerivedCategory.homologyFunctorFactors (PresheafWithTransfers.{u + 1} k) i).app K)
  let : QuasiIso (singularTotalUnitApp k K) := singularTotalUnitApp_quasiIso_of_homology K b h
  let d := singularPresheafDerivedCochainIso k K b
  have hd : η.app QK ≫ d.hom = singularPresheafDerivedCochainMap k (singularTotalUnitApp k K) b b :=
    singularPresheafDerivedCochainIso_unit k K b
  let : IsIso (singularPresheafDerivedCochainMap k (singularTotalUnitApp k K) b b) :=
    isIso_singularPresheafDerivedCochainMap_of_quasiIso k _ b b
  let : IsIso (η.app QK ≫ d.hom) := hd.symm ▸ inferInstance
  let : IsIso (η.app QK) := IsIso.of_isIso_comp_right _ d.hom
  have he : e.hom ≫ η.app X = η.app QK ≫ (singularPresheafDerivedFunctor k).map e.hom :=
    η.naturality e.hom
  let : IsIso (e.hom ≫ η.app X) := he.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left e.hom _

end AlgebraicGeometry.MotivicHomotopy

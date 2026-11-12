/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Polynomial.RationalCoordinateSection
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.ResidueIndependentSmoothMap
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # The actual marked intersection of the independent etale and retained opens

The independent chart D(re) is not assumed contained in the retained whole-fiber
open D(r). Their actual pullback intersection carries the original rational mark.
The section is constructed from the unchanged coordinate value.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
variable {B : Type u} [CommRing B]

/-- The true intersection of the localization chart and retained principal open. -/
abbrev quadraticRetainedEtaleChart (re r : B) : Scheme :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re))))
    (Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r))

/-- The marked intersection remains affine, with neither principal open replaced. -/
instance quadraticRetainedEtaleChart_isAffine (re r : B) :
    IsAffine (quadraticRetainedEtaleChart re r) := by
  have : IsAffine (Scheme.Opens.toScheme (X := Spec (.of B))
      (PrimeSpectrum.basicOpen r)) := IsAffineOpen.Spec_basicOpen (R := .of B) r
  infer_instance

/-- Both opens, the original rational mark, and the original coordinate tuple
produce actual EtaleChart data without a marking-compatibility hypothesis. -/
theorem exists_quadraticRetainedEtaleChart_data
    {E R : Type u} [Field E] [CommRing R] [Algebra E R] [Algebra E B]
    (f : Polynomial R →ₐ[E] B) (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _)
    (re r : B) (hre : re ∉ (x default).asIdeal) (hr : r ∉ (x default).asIdeal)
    (he : ((algebraMap B (Localization.Away re)).comp f.toRingHom).Etale) :
    let je := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re)))
    let jr := Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)
    let q := pullback.fst je jr ≫ je ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
    let p := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
    let i := pullback.snd je jr
    let u := jr ≫ Spec.map (CommRingCat.ofHom (f.toRingHom.comp Polynomial.C))
    Etale q ∧ IsOpenImmersion i ∧ SmoothOfRelativeDimension 1 p ∧ i ≫ u = q ≫ p ∧
    ∃ (s : Spec (.of R) ⟶ Spec (.of (Polynomial R)))
      (η : Spec (.of E) ⟶ Spec (.of R))
      (ξ : Spec (.of E) ⟶ quadraticRetainedEtaleChart re r),
      s ≫ p = 𝟙 _ ∧ ξ ≫ q = η ≫ s ∧ ξ ≫ i ≫ jr = x := by
  let je := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re)))
  let jr := Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)
  have hje : IsOpenImmersion je := by
    change IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re))))
    infer_instance
  let Ue : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen re
  let Ur : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen r
  have hjr : IsOpenImmersion jr :=
    IsOpenImmersion.ofRestrict (Spec (.of B)) Ur.isOpenEmbedding
  have hjeRange : Set.range je =
      (Ue : Set (Spec (.of B))) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away re) re
  have hjrRange : Set.range jr =
      (Ur : Set (Spec (.of B))) :=
    Scheme.Opens.range_ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)
  have hxe : Set.range x ⊆ Set.range je := by
    rintro _ ⟨z, rfl⟩
    apply (Set.ext_iff.mp hjeRange (x z)).mpr
    change re ∉ (x z).asIdeal
    exact Eq.mpr (congrArg (fun a : Spec (.of E) => re ∉ (x a).asIdeal)
      (Subsingleton.elim z default)) hre
  have hxr : Set.range x ⊆ Set.range jr := by
    rintro _ ⟨z, rfl⟩
    apply (Set.ext_iff.mp hjrRange (x z)).mpr
    change r ∉ (x z).asIdeal
    exact Eq.mpr (congrArg (fun a : Spec (.of E) => r ∉ (x a).asIdeal)
      (Subsingleton.elim z default)) hr
  let xe := IsOpenImmersion.lift je x hxe
  let xr := IsOpenImmersion.lift jr x hxr
  have heq : xe ≫ je = x := IsOpenImmersion.lift_fac je x hxe
  have hrq : xr ≫ jr = x := IsOpenImmersion.lift_fac jr x hxr
  let ξ : Spec (.of E) ⟶ quadraticRetainedEtaleChart re r :=
    pullback.lift xe xr (heq.trans hrq.symm)
  have hcoord : je ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap B (Localization.Away re)).comp f.toRingHom)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hq : Etale (je ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    rw [hcoord]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he
  obtain ⟨s, η, hs, hmark⟩ := exists_polynomial_section_through_rational_schemePoint f x hx
  refine ⟨inferInstance, inferInstance, polynomialProjection_smooth_one R, ?_,
    s, η, ξ, hs, ?_, ?_⟩
  · let F : Spec (.of B) ⟶ Spec (.of (Polynomial R)) :=
      Spec.map (CommRingCat.ofHom f.toRingHom)
    let P : Spec (.of (Polynomial R)) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
    let T : Spec (.of B) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (f.toRingHom.comp Polynomial.C))
    have hT : T = F ≫ P := by
      dsimp only [T, F, P]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change pullback.snd je jr ≫ (jr ≫ T) =
      (pullback.fst je jr ≫ je ≫ F) ≫ P
    calc
      pullback.snd je jr ≫ (jr ≫ T) = (pullback.snd je jr ≫ jr) ≫ T :=
        (Category.assoc _ _ _).symm
      _ = (pullback.fst je jr ≫ je) ≫ T :=
        congrArg (fun z => z ≫ T) (pullback.condition (f := je) (g := jr)).symm
      _ = (pullback.fst je jr ≫ je) ≫ (F ≫ P) :=
        congrArg (fun z => (pullback.fst je jr ≫ je) ≫ z) hT
      _ = ((pullback.fst je jr ≫ je) ≫ F) ≫ P :=
        (Category.assoc _ _ _).symm
      _ = (pullback.fst je jr ≫ je ≫ F) ≫ P :=
        congrArg (fun z => z ≫ P) (Category.assoc _ _ _)
  · change ξ ≫ (pullback.fst je jr ≫ je ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) = η ≫ s
    have hfst : ξ ≫ pullback.fst je jr = xe := pullback.lift_fst _ _ _
    rw [← Category.assoc, hfst, ← Category.assoc, heq]
    exact hmark
  · change ξ ≫ (pullback.snd je jr ≫ jr) = x
    have hsnd : ξ ≫ pullback.snd je jr = xr := pullback.lift_snd _ _ _
    rw [← Category.assoc, hsnd]
    exact hrq
end AlgebraicGeometry.Scheme

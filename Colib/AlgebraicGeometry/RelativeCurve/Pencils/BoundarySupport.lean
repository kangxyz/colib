/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FiniteFlatZeros
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedProductFamily
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# Whole-boundary frames control the entire polynomial family

Two sections agreeing on the whole boundary have a polynomial interpolation whose
restriction to that whole boundary is constant. If the common section is carried to
one by a boundary frame, its zero ideal is the unit ideal there. The whole family
therefore lies in the original retained curve open, including at every parameter.
Properness of the compactification and the native relative-curve Cartier criterion
then prove finiteness and flatness of the whole restricted polynomial zero scheme.

This module does not assume a supplied homotopy, finite-flat family, regular section,
or support-avoidance conclusion. It consumes actual boundary frames and section
restrictions. Producing those frames and prescribed sections from the marked
presentation remains a separate geometric obligation.

The original polynomial support argument is
`Motivic/Aglib/AlgebraicGeometry/Modules/Invertible/Pencils/PolynomialBoundaryPencil.lean`,
blob `255fab996ba506779802f3f921fb40d88c258ebc`, at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- A section evaluated to one by an actual module functional has the unit zero ideal.
In particular this applies to the inverse of a boundary frame. -/
theorem zeroScheme_eq_top_of_unit_evaluation {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (a : Γ(L, ⊤)) (e : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (he : e.app ⊤ a = (1 : Γ(X, ⊤))) : zeroScheme X L a = ⊤ := by
  apply Scheme.IdealSheafData.ext
  funext U
  change (zeroScheme X L a).ideal U = ⊤
  rw [zeroScheme_ideal, Ideal.eq_top_iff_one]
  apply Ideal.subset_span
  refine ⟨Scheme.Modules.sectionsLinearMap e U.1, ?_⟩
  let res := (homOfLE (le_top : U.1 ≤ ⊤)).op
  have hn := PresheafOfModules.naturality_apply e.val res a
  change @Eq Γ(X, U.1) (e.app U.1 (L.presheaf.map res a))
    (X.presheaf.map res (e.app ⊤ a)) at hn
  change @Eq Γ(X, ⊤) (e.app ⊤ a) 1 at he
  rw [he, map_one] at hn
  exact hn.symm

/-- A whole boundary with unit inverse-image ideal is disjoint from the whole support.
The covering hypothesis is on all points of the original ambient scheme. -/
theorem whole_support_subset_of_boundary_comap_top {C X Z : Scheme.{u}}
    (j : C ⟶ X) (i : Z ⟶ X) (I : X.IdealSheafData)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (hI : I.comap i = ⊤) : Set.range I.subschemeι ⊆ Set.range j := by
  intro x hx
  have hs : x ∈ I.support := by rwa [I.range_subschemeι] at hx
  rcases hcover x with hj | ⟨z, rfl⟩
  · exact hj
  · have hz : z ∈ (I.comap i).support := by
      rw [Scheme.IdealSheafData.support_comap]
      exact hs
    rw [hI, Scheme.IdealSheafData.support_top] at hz
    exact False.elim hz

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace AlgebraicGeometry.Scheme.PolynomialSectionPencil

open RelativeCurvePencil

variable {R : Type u} [CommRing R] {X Z : Scheme.{u}}
  (b : X ⟶ Spec (.of R)) (i : Z ⟶ X) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (a c : Γ(L, ⊤))

omit [AlgebraicGeometry.SheafOfModules.IsInvertible
  X.sheaf.obj X.ringCatSheaf.property L] in
/-- Equality on the whole original boundary persists on its whole parameter space. -/
theorem parameterBoundary_pullback_eq
    (h : pullbackGlobalSections i L a = pullbackGlobalSections i L c) :
    pullbackGlobalSections (parameterMap b i) ((Modules.pullback (projection b)).obj L)
        (pullbackGlobalSections (projection b) L a) =
      pullbackGlobalSections (parameterMap b i) ((Modules.pullback (projection b)).obj L)
        (pullbackGlobalSections (projection b) L c) := by
  apply pullbackGlobalSections_injective_pullbackComp (parameterMap b i) (projection b) L
  change ((Modules.pullbackComp (parameterMap b i) (projection b)).hom.app L).app ⊤
      (pullbackGlobalSections (parameterMap b i) ((Modules.pullback (projection b)).obj L)
        (pullbackGlobalSections (projection b) L a)) =
    ((Modules.pullbackComp (parameterMap b i) (projection b)).hom.app L).app ⊤
      (pullbackGlobalSections (parameterMap b i) ((Modules.pullback (projection b)).obj L)
        (pullbackGlobalSections (projection b) L c))
  rw [SectionsEqualizer.pullbackGlobalSections_comp,
    SectionsEqualizer.pullbackGlobalSections_comp, parameterMap_projection,
    ← SectionsEqualizer.pullbackGlobalSections_comp,
    ← SectionsEqualizer.pullbackGlobalSections_comp, h]

/-- The actual polynomial zero ideal restricts to the constant zero ideal on a boundary
where the two original sections agree, with the complete scheme structures retained. -/
theorem familyZero_comap_boundary
    (h : pullbackGlobalSections i L a = pullbackGlobalSections i L c) :
    (familyZero b L a c).comap (parameterMap b i) =
      ((zeroScheme X L a).comap i).comap (projection (i ≫ b)) := by
  have hp := parameterBoundary_pullback_eq b i L a c h
  rw [familyZero, ← Stacks.Divisors.zeroScheme_pullback]
  have hf : pullbackGlobalSections (parameterMap b i)
        ((Modules.pullback (projection b)).obj L) (familySection b L a c) =
      pullbackGlobalSections (parameterMap b i)
        ((Modules.pullback (projection b)).obj L)
        (pullbackGlobalSections (projection b) L a) := by
    simp only [familySection, map_add, map_sub,
      SectionsEqualizer.pullbackGlobalSections_smul, hp, sub_self, smul_zero, add_zero]
  rw [hf, Stacks.Divisors.zeroScheme_pullback, Stacks.Divisors.zeroScheme_pullback,
    ← Scheme.IdealSheafData.comap_comp, parameterMap_projection,
    Scheme.IdealSheafData.comap_comp]

/-- The entire polynomial boundary has unit zero ideal when its common prescribed
section is a genuine boundary frame. -/
theorem familyZero_comap_boundary_eq_top
    (h : pullbackGlobalSections i L a = pullbackGlobalSections i L c)
    (e : (Modules.pullback i).obj L ⟶ SheafOfModules.unit Z.ringCatSheaf)
    (he : e.app ⊤ (pullbackGlobalSections i L a) = (1 : Γ(Z, ⊤))) :
    (familyZero b L a c).comap (parameterMap b i) = ⊤ := by
  rw [familyZero_comap_boundary b i L a c h, ← Stacks.Divisors.zeroScheme_pullback]
  have hzero := zeroScheme_eq_top_of_unit_evaluation _ _ e he
  exact (congrArg (fun I : Z.IdealSheafData => I.comap (projection (i ≫ b))) hzero).trans
    (Scheme.IdealSheafData.comap_top _)

/-- The parameter-map image is the full inverse image of the original image. -/
theorem range_parameterMap :
    Set.range (parameterMap b i) = projection b ⁻¹' Set.range i := by
  simpa using Scheme.image_preimage_eq_of_isPullback (parameterMap_isPullback b i) Set.univ

/-- A whole original open/boundary cover pulls back to a whole parameter-space cover. -/
theorem parameter_boundary_cover {C : Scheme.{u}} (j : C ⟶ X)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i) :
    ∀ x : parameterSpace b,
      x ∈ Set.range (parameterMap b j) ∨ x ∈ Set.range (parameterMap b i) := by
  intro x
  simpa only [range_parameterMap, Set.mem_preimage] using hcover (projection b x)

/-- Whole-boundary equality and a frame force the whole polynomial support into the
original retained open, uniformly over every parameter. -/
theorem familyZero_whole_support_subset {C : Scheme.{u}} (j : C ⟶ X)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (h : pullbackGlobalSections i L a = pullbackGlobalSections i L c)
    (e : (Modules.pullback i).obj L ⟶ SheafOfModules.unit Z.ringCatSheaf)
    (he : e.app ⊤ (pullbackGlobalSections i L a) = (1 : Γ(Z, ⊤))) :
    Set.range (familyZero b L a c).subschemeι ⊆ Set.range (parameterMap b j) :=
  whole_support_subset_of_boundary_comap_top (parameterMap b j) (parameterMap b i) _
    (parameter_boundary_cover b i j hcover) (familyZero_comap_boundary_eq_top b i L a c h e he)

/-- The whole polynomial zero scheme on the retained curve is finite and relative Cartier.
Its whole flatness follows, rather than being supplied. The compactification is only proper,
and the boundary covers its entire complement, not merely a dense set. -/
theorem finite_relativeCartier_family_on_open_of_boundary_frame
    {S C : Scheme.{u}} (bS : S ⟶ Spec (.of R)) (f : X ⟶ S) [IsProper f] [IsAffine S]
    (j : C ⟶ X) [IsOpenImmersion j] [C.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ f)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (h : pullbackGlobalSections i L a = pullbackGlobalSections i L c)
    (e : (Modules.pullback i).obj L ⟶ SheafOfModules.unit Z.ringCatSheaf)
    (he : e.app ⊤ (pullbackGlobalSections i L a) = (1 : Γ(Z, ⊤))) :
    IsFinite (((familyZero (f ≫ bS) L a c).comap (parameterMap (f ≫ bS) j)).subschemeι ≫
      (parameterMap (f ≫ bS) j ≫ parameterMap bS f)) ∧
      Stacks.Divisors.IsRelativeEffectiveCartierDivisor
        (parameterMap (f ≫ bS) j ≫ parameterMap bS f)
        ((familyZero (f ≫ bS) L a c).comap (parameterMap (f ≫ bS) j)) := by
  have : IsProper (parameterMap bS f) :=
    MorphismProperty.of_isPullback (parameterMap_isPullback bS f) inferInstance
  have : IsOpenImmersion (parameterMap (f ≫ bS) j) :=
    MorphismProperty.of_isPullback (parameterMap_isPullback (f ≫ bS) j) inferInstance
  have : SmoothOfRelativeDimension 1
      (parameterMap (f ≫ bS) j ≫ parameterMap bS f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      ((parameterMap_isPullback (f ≫ bS) j).paste_vert
        (parameterMap_isPullback bS f)) inferInstance
  have : IsAffine (parameterSpace bS) :=
    isAffine_of_isAffineHom (projection bS)
  have : IsAffineHom (projection (j ≫ (f ≫ bS))) := by
    let p := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
    have hp : IsAffineHom p := isAffineHom_of_isAffine _
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (j ≫ (f ≫ bS)) p).flip hp
  have : (parameterSpace (j ≫ (f ≫ bS))).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom (projection (j ≫ (f ≫ bS)))
  exact finite_relativeCartier_on_open_of_proper (parameterMap bS f)
    (parameterMap (f ≫ bS) j) (familyZero (f ≫ bS) L a c)
    (isLocallyPrincipal_zeroScheme _ _ _)
    (familyZero_whole_support_subset (f ≫ bS) i L a c j hcover h e he)

end AlgebraicGeometry.Scheme.PolynomialSectionPencil

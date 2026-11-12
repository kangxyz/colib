/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.CartesianSquare

/-!
# Polynomial pencils of sections in the native invertible-module model

The polynomial spectrum is only the comparison coordinate for the existing native additive
parameter. Sections and zero schemes are the pinned Stacks objects, including their full
scheme structures. Endpoint identities below are equalities of ideal sheaves, not merely
pointwise support equalities.

The polynomial coordinate construction is adapted from
`Motivic/Aglib/AlgebraicGeometry/Modules/Invertible/Pencils/PolynomialBoundaryPencil.lean`
blob `255fab996ba506779802f3f921fb40d88c258ebc`, at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
The former Aglib line-bundle and zero-functional model is not imported.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Divisors
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.PolynomialSectionPencil

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (b : X ⟶ Spec (.of R))

/-- This is literally the polynomial line used by finite correspondences. -/
abbrev parameterSpace :=
  Limits.pullback b (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))

/-- The first projection from the polynomial parameter line to the original scheme. -/
abbrev projection : parameterSpace b ⟶ X := pullback.fst _ _

/-- Its actual global polynomial coordinate. -/
def parameter : Γ(parameterSpace b, ⊤) :=
  (pullback.snd b (Spec.map (CommRingCat.ofHom Polynomial.C))).appTop
    ((Scheme.ΓSpecIso (.of R[X])).inv Polynomial.X)

/-- Actual scalar-evaluation section. -/
def endpoint (c : R) : X ⟶ parameterSpace b :=
  pullback.lift (𝟙 X) (b ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))) (by
    simp only [Category.id_comp, Category.assoc, ← Spec.map_comp]
    have he : CommRingCat.ofHom (Polynomial.C : R →+* R[X]) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom c) = 𝟙 (CommRingCat.of R) := by
      ext r
      exact Polynomial.eval_C
    rw [he, Spec.map_id, Category.comp_id])

@[reassoc (attr := simp)] theorem endpoint_projection (c : R) :
    endpoint b c ≫ projection b = 𝟙 X := pullback.lift_fst _ _ _

@[simp] theorem endpoint_parameter (c : R) :
    (endpoint b c).appTop (parameter b) = b.appTop ((Scheme.ΓSpecIso (.of R)).inv c) := by
  change ((endpoint b c).appTop)
    ((pullback.snd b _).appTop ((Scheme.ΓSpecIso (.of R[X])).inv Polynomial.X)) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, endpoint, pullback.lift_snd,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  apply congrArg (fun x ↦ b.appTop x)
  have hh := (congrArg (fun f : CommRingCat.of R[X] ⟶ Γ(Spec (.of R), ⊤) ↦ f Polynomial.X)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Polynomial.evalRingHom c)))).symm
  change (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))).appTop
      ((Scheme.ΓSpecIso (.of R[X])).inv Polynomial.X) =
    (Scheme.ΓSpecIso (.of R)).inv ((Polynomial.evalRingHom c) Polynomial.X) at hh
  simpa using hh

/-- The actual linear pencil of two sections, on the full polynomial parameter scheme. -/
def familySection (L : X.Modules) (a c : Γ(L, ⊤)) :
    Γ((Modules.pullback (projection b)).obj L, ⊤) :=
  pullbackGlobalSections (projection b) L a +
    parameter b • (pullbackGlobalSections (projection b) L c -
      pullbackGlobalSections (projection b) L a)

/-- Restricting the polynomial section at zero gives the first pulled-back section. -/
theorem familySection_zero (L : X.Modules) (a c : Γ(L, ⊤)) :
    pullbackGlobalSections (endpoint b 0) ((Modules.pullback (projection b)).obj L)
        (familySection b L a c) =
      pullbackGlobalSections (endpoint b 0) ((Modules.pullback (projection b)).obj L)
        (pullbackGlobalSections (projection b) L a) := by
  simp only [familySection, map_add, SectionsEqualizer.pullbackGlobalSections_smul,
    endpoint_parameter, map_zero, zero_smul, add_zero]

/-- Restricting the polynomial section at one gives the second pulled-back section. -/
theorem familySection_one (L : X.Modules) (a c : Γ(L, ⊤)) :
    pullbackGlobalSections (endpoint b 1) ((Modules.pullback (projection b)).obj L)
        (familySection b L a c) =
      pullbackGlobalSections (endpoint b 1) ((Modules.pullback (projection b)).obj L)
        (pullbackGlobalSections (projection b) L c) := by
  simp only [familySection, map_add, SectionsEqualizer.pullbackGlobalSections_smul,
    endpoint_parameter, map_one, one_smul, map_sub]
  abel

variable (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (a c : Γ(L, ⊤))

/-- The full native zero ideal of the polynomial family, before any reduction. -/
def familyZero : (parameterSpace b).IdealSheafData :=
  zeroScheme (parameterSpace b) ((Modules.pullback (projection b)).obj L)
    (familySection b L a c)

/-- The zero endpoint is the original zero ideal, with all nilpotents retained. -/
theorem familyZero_comap_zero :
    (familyZero b L a c).comap (endpoint b 0) = zeroScheme X L a := by
  rw [familyZero, ← Stacks.Divisors.zeroScheme_pullback, familySection_zero,
    Stacks.Divisors.zeroScheme_pullback, Stacks.Divisors.zeroScheme_pullback,
    ← IdealSheafData.comap_comp, endpoint_projection, IdealSheafData.comap_id]

/-- The one endpoint is the second original zero ideal, with all nilpotents retained. -/
theorem familyZero_comap_one :
    (familyZero b L a c).comap (endpoint b 1) = zeroScheme X L c := by
  rw [familyZero, ← Stacks.Divisors.zeroScheme_pullback, familySection_one,
    Stacks.Divisors.zeroScheme_pullback, Stacks.Divisors.zeroScheme_pullback,
    ← IdealSheafData.comap_comp, endpoint_projection, IdealSheafData.comap_id]

/-- The whole zero fiber, not just its reduced support, is the original zero scheme. -/
def zeroFiberIso : pullback (endpoint b 0) (familyZero b L a c).subschemeι ≅
    (zeroScheme X L a).subscheme :=
  ((familyZero b L a c).comapIso (endpoint b 0)).symm ≪≫
    eqToIso (congrArg IdealSheafData.subscheme (familyZero_comap_zero b L a c))

/-- The whole one fiber, not just its reduced support, is the original zero scheme. -/
def oneFiberIso : pullback (endpoint b 1) (familyZero b L a c).subschemeι ≅
    (zeroScheme X L c).subscheme :=
  ((familyZero b L a c).comapIso (endpoint b 1)).symm ≪≫
    eqToIso (congrArg IdealSheafData.subscheme (familyZero_comap_one b L a c))

private theorem subscheme_eqToHom_inclusion {Y : Scheme.{u}}
    {I J : Y.IdealSheafData} (h : I = J) :
    eqToHom (congrArg IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

/-- The zero-fiber identification preserves the actual map to the unchanged ambient scheme. -/
@[reassoc (attr := simp)]
theorem zeroFiberIso_hom_inclusion :
    (zeroFiberIso b L a c).hom ≫ (zeroScheme X L a).subschemeι =
      pullback.fst (endpoint b 0) (familyZero b L a c).subschemeι := by
  simp only [zeroFiberIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
  rw [subscheme_eqToHom_inclusion (familyZero_comap_zero b L a c)]
  exact IdealSheafData.comapIso_inv_subschemeι _ _

/-- The one-fiber identification preserves the actual map to the unchanged ambient scheme. -/
@[reassoc (attr := simp)]
theorem oneFiberIso_hom_inclusion :
    (oneFiberIso b L a c).hom ≫ (zeroScheme X L c).subschemeι =
      pullback.fst (endpoint b 1) (familyZero b L a c).subschemeι := by
  simp only [oneFiberIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc]
  rw [subscheme_eqToHom_inclusion (familyZero_comap_one b L a c)]
  exact IdealSheafData.comapIso_inv_subschemeι _ _

/-- The zero-fiber identification also preserves the original total-family projection. -/
@[reassoc]
theorem zeroFiberIso_hom_total :
    (zeroFiberIso b L a c).hom ≫ (zeroScheme X L a).subschemeι =
      pullback.snd (endpoint b 0) (familyZero b L a c).subschemeι ≫
        (familyZero b L a c).subschemeι ≫ projection b := by
  rw [zeroFiberIso_hom_inclusion, ← Category.assoc,
    ← pullback.condition, Category.assoc, endpoint_projection, Category.comp_id]

/-- The one-fiber identification also preserves the original total-family projection. -/
@[reassoc]
theorem oneFiberIso_hom_total :
    (oneFiberIso b L a c).hom ≫ (zeroScheme X L c).subschemeι =
      pullback.snd (endpoint b 1) (familyZero b L a c).subschemeι ≫
        (familyZero b L a c).subschemeι ≫ projection b := by
  rw [oneFiberIso_hom_inclusion, ← Category.assoc,
    ← pullback.condition, Category.assoc, endpoint_projection, Category.comp_id]

section NativeParameter

variable (R : CommRingCat.{u}) (U : SmoothSite (Spec R))

/-- The existing native additive cylinder is compared with this polynomial coordinate. -/
def nativeParameterIso :
    (SmoothSite.Contraction.affineLineCylinder.obj U).left ≅ parameterSpace U.hom :=
  (SmoothSite.forgetScheme (Spec R)).mapIso
    (SmoothSite.Contraction.affineCylinderPolynomialIso R U)

/-- The comparison preserves the literal evaluation map, including zero and one. -/
@[reassoc]
theorem nativeSection_parameterIso (r : R) :
    (SmoothSite.Contraction.nativeAffineSection R U r).left ≫
        (nativeParameterIso R U).hom = endpoint U.hom r := by
  have h := congrArg (fun q => q.left)
    (SmoothSite.Contraction.nativeAffineSection_polynomialIso R U r)
  exact h

end NativeParameter

end AlgebraicGeometry.Scheme.PolynomialSectionPencil

/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedProductFamily
public import Colib.AlgebraicGeometry.Correspondences.Graph.WholeFiniteFlatEndpoint

/-!
# Literal polynomial zero fibers of the existing native cylinder

These are only actual Cartesian transports of the previously constructed full
zero-scheme isomorphisms. Both the source projection and the original inclusion
are retained. They do not alter the pencil, its boundary sections, or its span.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.PolynomialSectionPencil

open SmoothSite.Contraction

variable {k : Type u} [Field k] (U : SmoothSite (Spec (.of k)))

/-- Actual change of parameter on the entire source-section fiber. -/
def nativeFiberParameterIso {D : Scheme.{u}} (r : k) (p : D ⟶ parameterSpace U.hom) :
    pullback (nativeAffineSection (.of k) U r).left
      (p ≫ (nativeParameterIso (.of k) U).inv) ≅ pullback (endpoint U.hom r) p :=
  asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (nativeParameterIso (.of k) U).hom
    (by simpa only [Category.id_comp] using (nativeSection_parameterIso (.of k) U r))
    (by simp))

@[reassoc (attr := simp)] theorem nativeFiberParameterIso_hom_fst
    {D : Scheme.{u}} (r : k) (p : D ⟶ parameterSpace U.hom) :
    (nativeFiberParameterIso U r p).hom ≫ pullback.fst (endpoint U.hom r) p =
      pullback.fst (nativeAffineSection (.of k) U r).left
        (p ≫ (nativeParameterIso (.of k) U).inv) := by
  simp [nativeFiberParameterIso, pullback.map]

@[reassoc (attr := simp)] theorem nativeFiberParameterIso_hom_snd
    {D : Scheme.{u}} (r : k) (p : D ⟶ parameterSpace U.hom) :
    (nativeFiberParameterIso U r p).hom ≫ pullback.snd (endpoint U.hom r) p =
      pullback.snd (nativeAffineSection (.of k) U r).left
        (p ≫ (nativeParameterIso (.of k) U).inv) := by
  simp [nativeFiberParameterIso, pullback.map]

variable {C : Scheme.{u}} (p : C ⟶ U.left) (L : C.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
  (a c : Γ(L, ⊤))

/-- The actual native zero fiber, with all nilpotents. -/
def nativeZeroFiberIso :
    pullback (nativeAffineSection (.of k) U 0).left
      (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv) ≅
        (zeroScheme C L a).subscheme :=
  nativeFiberParameterIso U 0 (familySource U.hom p L a c) ≪≫
    zeroFiberOverBaseIso U.hom p L a c

/-- The actual native one fiber, with all nilpotents. -/
def nativeOneFiberIso :
    pullback (nativeAffineSection (.of k) U 1).left
      (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv) ≅
        (zeroScheme C L c).subscheme :=
  nativeFiberParameterIso U 1 (familySource U.hom p L a c) ≪≫
    oneFiberOverBaseIso U.hom p L a c

@[reassoc (attr := simp)] theorem nativeZeroFiberIso_hom_base :
    (nativeZeroFiberIso U p L a c).hom ≫ (zeroScheme C L a).subschemeι ≫ p =
      pullback.fst (nativeAffineSection (.of k) U 0).left
        (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv) := by
  simp only [nativeZeroFiberIso, Iso.trans_hom, Category.assoc,
    zeroFiberOverBaseIso_hom_base, nativeFiberParameterIso_hom_fst]

@[reassoc (attr := simp)] theorem nativeOneFiberIso_hom_base :
    (nativeOneFiberIso U p L a c).hom ≫ (zeroScheme C L c).subschemeι ≫ p =
      pullback.fst (nativeAffineSection (.of k) U 1).left
        (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv) := by
  simp only [nativeOneFiberIso, Iso.trans_hom, Category.assoc,
    oneFiberOverBaseIso_hom_base, nativeFiberParameterIso_hom_fst]

@[reassoc (attr := simp)] theorem nativeZeroFiberIso_hom_original :
    (nativeZeroFiberIso U p L a c).hom ≫ (zeroScheme C L a).subschemeι =
      pullback.snd (nativeAffineSection (.of k) U 0).left
        (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv) ≫
          (familyZero (p ≫ U.hom) L a c).subschemeι ≫ projection (p ≫ U.hom) := by
  simp only [nativeZeroFiberIso, Iso.trans_hom, Category.assoc,
    zeroFiberOverBaseIso_hom_original, nativeFiberParameterIso_hom_snd_assoc]

@[reassoc (attr := simp)] theorem nativeOneFiberIso_hom_original :
    (nativeOneFiberIso U p L a c).hom ≫ (zeroScheme C L c).subschemeι =
      pullback.snd (nativeAffineSection (.of k) U 1).left
        (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv) ≫
          (familyZero (p ≫ U.hom) L a c).subschemeι ≫ projection (p ≫ U.hom) := by
  simp only [nativeOneFiberIso, Iso.trans_hom, Category.assoc,
    oneFiberOverBaseIso_hom_original, nativeFiberParameterIso_hom_snd_assoc]

/-- Finiteness at zero is inherited by the actual full Cartesian endpoint. -/
theorem nativeZeroSource_isFinite
    [IsFinite (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv)] :
    IsFinite ((zeroScheme C L a).subschemeι ≫ p) := by
  have h : (zeroScheme C L a).subschemeι ≫ p =
      (nativeZeroFiberIso U p L a c).inv ≫
        pullback.fst (nativeAffineSection (.of k) U 0).left
          (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv) := by
    rw [← nativeZeroFiberIso_hom_base U p L a c, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- Flatness at zero is inherited by the whole endpoint, not its components. -/
theorem nativeZeroSource_flat
    [Flat (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv)] :
    Flat ((zeroScheme C L a).subschemeι ≫ p) := by
  have h : (zeroScheme C L a).subschemeι ≫ p =
      (nativeZeroFiberIso U p L a c).inv ≫
        pullback.fst (nativeAffineSection (.of k) U 0).left
          (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv) := by
    rw [← nativeZeroFiberIso_hom_base U p L a c, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- Finiteness at one is inherited by the actual full Cartesian endpoint. -/
theorem nativeOneSource_isFinite
    [IsFinite (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv)] :
    IsFinite ((zeroScheme C L c).subschemeι ≫ p) := by
  have h : (zeroScheme C L c).subschemeι ≫ p =
      (nativeOneFiberIso U p L a c).inv ≫
        pullback.fst (nativeAffineSection (.of k) U 1).left
          (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv) := by
    rw [← nativeOneFiberIso_hom_base U p L a c, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- Flatness at one is inherited by the whole endpoint, not its components. -/
theorem nativeOneSource_flat
    [Flat (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv)] :
    Flat ((zeroScheme C L c).subschemeι ≫ p) := by
  have h : (zeroScheme C L c).subschemeι ≫ p =
      (nativeOneFiberIso U p L a c).inv ≫
        pullback.fst (nativeAffineSection (.of k) U 1).left
          (familySource U.hom p L a c ≫ (nativeParameterIso (.of k) U).inv) := by
    rw [← nativeOneFiberIso_hom_base U p L a c, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

end AlgebraicGeometry.Scheme.PolynomialSectionPencil

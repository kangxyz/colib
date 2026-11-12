/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.BaseChange.NativeParameters

/-! # Cross-field comparisons for the actual native line and torus cylinders

The field functor is the actual scheme pullback. Both cylinder isomorphisms are
its product comparison followed by the integral native-parameter comparison.
They preserve naturality, both projections, the whole native zero section and
the positive Laurent open. No polynomial or Laurent model becomes active.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

section SchemeBase
variable {S T : Scheme.{u}} (r : T ⟶ S)

/-- A literal isomorphism of the second product factor. -/
def parameterRightIso (X : SmoothSite T) {A B : SmoothSite T} (e : A ≅ B) :
    product X A ≅ product X B where
  hom := productMap (𝟙 X) e.hom
  inv := productMap (𝟙 X) e.inv
  hom_inv_id := by rw [← productMap_comp]; simp
  inv_hom_id := by rw [← productMap_comp]; simp

/-- Base change of a product followed by a specified genuine parameter comparison. -/
def baseChangeParameterProductIso (X A : SmoothSite S) {B : SmoothSite T}
    (e : (baseChange r).obj A ≅ B) :
    (baseChange r).obj (product X A) ≅ product ((baseChange r).obj X) B :=
  baseChangeProductIso r X A ≪≫ parameterRightIso ((baseChange r).obj X) e

@[reassoc (attr := simp)] theorem baseChangeParameterProductIso_fst
    (X A : SmoothSite S) {B : SmoothSite T} (e : (baseChange r).obj A ≅ B) :
    (baseChangeParameterProductIso r X A e).hom ≫ productFst ((baseChange r).obj X) B =
      (baseChange r).map (productFst X A) := by
  simp only [baseChangeParameterProductIso, parameterRightIso, Iso.trans_hom,
    Category.assoc, productMap_fst, Category.comp_id, baseChangeProductIso_fst]

@[reassoc (attr := simp)] theorem baseChangeParameterProductIso_snd
    (X A : SmoothSite S) {B : SmoothSite T} (e : (baseChange r).obj A ≅ B) :
    (baseChangeParameterProductIso r X A e).hom ≫ productSnd ((baseChange r).obj X) B =
      (baseChange r).map (productSnd X A) ≫ e.hom := by
  simp only [baseChangeParameterProductIso, parameterRightIso, Iso.trans_hom,
    Category.assoc, productMap_snd, baseChangeProductIso_snd_assoc]

@[reassoc] theorem baseChangeParameterProductIso_naturality
    {X Y : SmoothSite S} (f : X ⟶ Y) (A : SmoothSite S) {B : SmoothSite T}
    (e : (baseChange r).obj A ≅ B) :
    (baseChange r).map (productMap f (𝟙 A)) ≫
        (baseChangeParameterProductIso r Y A e).hom =
      (baseChangeParameterProductIso r X A e).hom ≫
        productMap ((baseChange r).map f) (𝟙 B) := by
  apply product_hom_ext
  · simp only [Category.assoc, baseChangeParameterProductIso_fst,
      baseChangeParameterProductIso_fst_assoc,
      productMap_fst, ← Functor.map_comp, productMap_fst]
  · simp only [Category.assoc, baseChangeParameterProductIso_snd,
      productMap_snd, Category.comp_id, ← Functor.map_comp_assoc,
      productMap_snd, Category.comp_id]

/-- The actual native additive cylinder comparison for every base morphism. -/
def nativeA1BaseChangeIso (X : SmoothSite S) :
    (baseChange r).obj (Contraction.affineLineCylinder.obj X) ≅
      Contraction.affineLineCylinder.obj ((baseChange r).obj X) :=
  baseChangeParameterProductIso r X (additiveGroupObject S) (nativeAdditiveBaseChangeIso r)

/-- The actual native multiplicative cylinder comparison for every base morphism. -/
def nativeTorusBaseChangeIso (X : SmoothSite S) :
    (baseChange r).obj (Contraction.torusCylinder.obj X) ≅
      Contraction.torusCylinder.obj ((baseChange r).obj X) :=
  baseChangeParameterProductIso r X (multiplicativeGroupObject S)
    (nativeMultiplicativeBaseChangeIso r)

/-- Naturality preserves the original forward Laurent open, not its inverse. -/
@[reassoc] theorem nativeA1BaseChangeIso_open (X : SmoothSite S) :
    (baseChange r).map (Contraction.openInclusion.app X) ≫ (nativeA1BaseChangeIso r X).hom =
      (nativeTorusBaseChangeIso r X).hom ≫
        Contraction.openInclusion.app ((baseChange r).obj X) := by
  apply product_hom_ext
  · simp only [nativeA1BaseChangeIso, nativeTorusBaseChangeIso, Category.assoc,
      baseChangeParameterProductIso_fst, Contraction.openInclusion_app,
      productMap_fst, Category.comp_id, ← Functor.map_comp,
      productMap_fst, Category.comp_id]
  · simp only [nativeA1BaseChangeIso, nativeTorusBaseChangeIso, Category.assoc,
      baseChangeParameterProductIso_snd, baseChangeParameterProductIso_snd_assoc,
      Contraction.openInclusion_app,
      productMap_snd, ← Functor.map_comp_assoc, productMap_snd]
    rw [Functor.map_comp, Category.assoc, nativeParameterBaseChangeIso_open]

/-- The entire native zero section over an arbitrary ground scheme. -/
def nativeZeroSection (X : SmoothSite S) : X ⟶ Contraction.affineLineCylinder.obj X :=
  productLift (𝟙 X) (Contraction.toBase X ≫ nativeZeroPoint S)

/-- At a field or ring spectrum, it is the existing chosen native affine section. -/
theorem nativeZeroSection_spec (A : CommRingCat.{u}) (X : SmoothSite (Spec A)) :
    nativeZeroSection X = Contraction.nativeAffineSection A X 0 := by
  simp only [nativeZeroSection, nativeZeroPoint_spec, Contraction.nativeAffineSection]

/-- Arbitrary base change preserves the whole zero morphism, before choosing a point. -/
@[reassoc] theorem nativeA1BaseChangeIso_zero (X : SmoothSite S) :
    (baseChange r).map (nativeZeroSection X) ≫ (nativeA1BaseChangeIso r X).hom =
      nativeZeroSection ((baseChange r).obj X) := by
  apply product_hom_ext
  · simp only [nativeA1BaseChangeIso, Category.assoc,
      baseChangeParameterProductIso_fst, ← Functor.map_comp,
      nativeZeroSection, productLift_fst]
    exact (baseChange r).map_id X
  · simp only [nativeA1BaseChangeIso, Category.assoc,
      baseChangeParameterProductIso_snd, ← Functor.map_comp_assoc,
      nativeZeroSection, productLift_snd]
    rw [Functor.map_comp, Category.assoc, nativeParameterBaseChangeIso_zero,
      ← Category.assoc, baseChange_toBase]

end SchemeBase

section FieldBase
variable {k L : Type u} [Field k] [Field L] [Algebra k L]
local notation "r" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "F" => fieldBaseChange (algebraMap k L)

/-- The exact cross-field affine-cylinder comparison consumed by scalar polynomial coordinates. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/BaseChange/FieldBaseChangeA1.lean:47-50"
  "adaptation" "Actual native group cylinders under arbitrary field extension"]
def fieldBaseChangeA1Iso (X : SmoothSite (Spec (.of k))) :
    (F).obj (Contraction.affineLineCylinder.obj X) ≅
      Contraction.affineLineCylinder.obj ((F).obj X) := nativeA1BaseChangeIso r X

/-- The whole cross-field native torus, with the original positive coordinate. -/
def fieldBaseChangeTorusCylinderIso (X : SmoothSite (Spec (.of k))) :
    (F).obj (Contraction.torusCylinder.obj X) ≅
      Contraction.torusCylinder.obj ((F).obj X) := nativeTorusBaseChangeIso r X

@[reassoc (attr := simp)] theorem fieldBaseChangeA1Iso_projection
    (X : SmoothSite (Spec (.of k))) :
    (fieldBaseChangeA1Iso (L := L) X).hom ≫
      productFst ((F).obj X) (additiveGroupObject (Spec (.of L))) =
        (F).map (productFst X (additiveGroupObject (Spec (.of k)))) :=
  baseChangeParameterProductIso_fst r X (additiveGroupObject (Spec (.of k)))
    (nativeAdditiveBaseChangeIso r)

@[reassoc (attr := simp)] theorem fieldBaseChangeTorusCylinderIso_projection
    (X : SmoothSite (Spec (.of k))) :
    (fieldBaseChangeTorusCylinderIso (L := L) X).hom ≫
      productFst ((F).obj X) (multiplicativeGroupObject (Spec (.of L))) =
        (F).map (productFst X (multiplicativeGroupObject (Spec (.of k)))) :=
  baseChangeParameterProductIso_fst r X (multiplicativeGroupObject (Spec (.of k)))
    (nativeMultiplicativeBaseChangeIso r)

@[reassoc (attr := simp)] theorem fieldBaseChangeA1Iso_parameter
    (X : SmoothSite (Spec (.of k))) :
    (fieldBaseChangeA1Iso (L := L) X).hom ≫
      productSnd ((F).obj X) (additiveGroupObject (Spec (.of L))) =
    (F).map (productSnd X (additiveGroupObject (Spec (.of k)))) ≫
      (nativeAdditiveBaseChangeIso r).hom :=
  baseChangeParameterProductIso_snd r X (additiveGroupObject (Spec (.of k)))
    (nativeAdditiveBaseChangeIso r)

@[reassoc (attr := simp)] theorem fieldBaseChangeTorusCylinderIso_parameter
    (X : SmoothSite (Spec (.of k))) :
    (fieldBaseChangeTorusCylinderIso (L := L) X).hom ≫
      productSnd ((F).obj X) (multiplicativeGroupObject (Spec (.of L))) =
    (F).map (productSnd X (multiplicativeGroupObject (Spec (.of k)))) ≫
      (nativeMultiplicativeBaseChangeIso r).hom :=
  baseChangeParameterProductIso_snd r X (multiplicativeGroupObject (Spec (.of k)))
    (nativeMultiplicativeBaseChangeIso r)

@[reassoc] theorem fieldBaseChangeA1Iso_naturality
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (F).map (Contraction.affineLineCylinder.map f) ≫ (fieldBaseChangeA1Iso (L := L) Y).hom =
      (fieldBaseChangeA1Iso (L := L) X).hom ≫ Contraction.affineLineCylinder.map ((F).map f) :=
  baseChangeParameterProductIso_naturality r f (additiveGroupObject (Spec (.of k)))
    (nativeAdditiveBaseChangeIso r)

@[reassoc] theorem fieldBaseChangeTorusCylinderIso_naturality
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (F).map (Contraction.torusCylinder.map f) ≫ (fieldBaseChangeTorusCylinderIso (L := L) Y).hom =
      (fieldBaseChangeTorusCylinderIso (L := L) X).hom ≫
        Contraction.torusCylinder.map ((F).map f) :=
  baseChangeParameterProductIso_naturality r f (multiplicativeGroupObject (Spec (.of k)))
    (nativeMultiplicativeBaseChangeIso r)

/-- Literal base change of the entire native zero section. -/
@[reassoc] theorem fieldBaseChangeA1Iso_zero (X : SmoothSite (Spec (.of k))) :
    (F).map (Contraction.nativeAffineSection (.of k) X 0) ≫
        (fieldBaseChangeA1Iso (L := L) X).hom =
      Contraction.nativeAffineSection (.of L) ((F).obj X) 0 := by
  change (baseChange r).map (Contraction.nativeAffineSection (.of k) X 0) ≫
      (nativeA1BaseChangeIso r X).hom =
    Contraction.nativeAffineSection (.of L) ((baseChange r).obj X) 0
  simpa only [nativeZeroSection_spec] using nativeA1BaseChangeIso_zero r X

/-- Literal compatibility of the actual native positive puncture under field extension. -/
@[reassoc] theorem fieldBaseChangeA1Iso_contractionOpen (X : SmoothSite (Spec (.of k))) :
    (F).map (Contraction.openInclusion.app X) ≫ (fieldBaseChangeA1Iso (L := L) X).hom =
      (fieldBaseChangeTorusCylinderIso (L := L) X).hom ≫
        Contraction.openInclusion.app ((F).obj X) := nativeA1BaseChangeIso_open r X

end FieldBase
end AlgebraicGeometry.Scheme.SmoothSite

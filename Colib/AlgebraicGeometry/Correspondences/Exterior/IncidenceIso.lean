/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceCoordinates

/-!
# Native exterior incidence is the full original incidence times the parameter

The displayed isomorphism compares actual schemes, not their reductions or
fundamental cycles. The original incidence can be reducible or nonreduced.
The proof uses only the native support isomorphisms and pullback identities.
Tor multiplicities and finite residue degrees are separate obligations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceToProduct_first :
    nativeExteriorIncidenceToProduct X Y Z T z w hz hw ≫
      exteriorIncidenceProductFirst X Y Z T z w =
      nativeExteriorIncidenceFirst X Y Z T z w hz hw := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, exteriorIncidenceProductFirst_fst,
      exteriorIncidenceProductFirst_snd, nativeExteriorIncidenceToProduct_fst_assoc,
      nativeExteriorIncidenceOriginal_fst, nativeExteriorIncidenceToProduct_snd]

@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceToProduct_second :
    nativeExteriorIncidenceToProduct X Y Z T z w hz hw ≫
      exteriorIncidenceProductSecond X Y Z T z w =
      nativeExteriorIncidenceSecond X Y Z T z w hz hw := by
  apply pullback.hom_ext
  · simp only [Category.assoc, exteriorIncidenceProductSecond_fst,
      nativeExteriorIncidenceToProduct_fst_assoc, nativeExteriorIncidenceOriginal_snd]
  · simp only [Category.assoc, exteriorIncidenceProductSecond_snd,
      nativeExteriorIncidenceToProduct_snd]
    exact nativeExteriorIncidence_parameter X Y Z T z w hz hw

/-- The literal full incidence product is isomorphic to the actual native exterior incidence. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Incidence.lean:258-279"
  "adaptation"
  "Native integralComponentAt supports; full nonreduced incidence and all components retained"]
def nativeExteriorIncidenceIso : exteriorIncidenceProduct X Y Z T z w ≅
    nativeExteriorIncidence X Y Z T z w hz hw where
  hom := exteriorIncidenceProductToNative X Y Z T z w hz hw
  inv := nativeExteriorIncidenceToProduct X Y Z T z w hz hw
  hom_inv_id := by
    apply exteriorIncidenceProduct_hom_ext X Y Z T z w
    · simp only [Category.assoc, SmoothSite.product_hom, nativeExteriorIncidenceToProduct_first,
        nativeExteriorIncidenceFirst, exteriorIncidenceProductToNative_fst_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, SmoothSite.product_hom, nativeExteriorIncidenceToProduct_second,
        nativeExteriorIncidenceSecond, exteriorIncidenceProductToNative_snd_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, SmoothSite.product_hom, exteriorIncidenceProductToNative_fst,
        nativeExteriorIncidenceToProduct_first_assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, SmoothSite.product_hom, exteriorIncidenceProductToNative_snd,
        nativeExteriorIncidenceToProduct_second_assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]

@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceIso_hom_fst :
    (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom ≫
      pullback.fst
        ((integralComponentAt
          (X := pullback (pullback.fst X.hom T.hom ≫ X.hom)
            (pullback.fst Y.hom T.hom ≫ Y.hom))
          (nativeExteriorPoint X Y T z hz)).subschemeι ≫
            pullback.snd (pullback.fst X.hom T.hom ≫ X.hom)
              (pullback.fst Y.hom T.hom ≫ Y.hom))
        ((integralComponentAt
          (X := pullback (pullback.fst Y.hom T.hom ≫ Y.hom)
            (pullback.fst Z.hom T.hom ≫ Z.hom))
          (nativeExteriorPoint Y Z T w hw)).subschemeι ≫
            pullback.fst (pullback.fst Y.hom T.hom ≫ Y.hom)
              (pullback.fst Z.hom T.hom ≫ Z.hom)) =
      exteriorIncidenceProductFirst X Y Z T z w ≫
        (nativeExteriorSupportIso X Y T z hz).hom :=
  exteriorIncidenceProductToNative_fst X Y Z T z w hz hw

@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceIso_hom_snd :
    (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom ≫
      pullback.snd
        ((integralComponentAt
          (X := pullback (pullback.fst X.hom T.hom ≫ X.hom)
            (pullback.fst Y.hom T.hom ≫ Y.hom))
          (nativeExteriorPoint X Y T z hz)).subschemeι ≫
            pullback.snd (pullback.fst X.hom T.hom ≫ X.hom)
              (pullback.fst Y.hom T.hom ≫ Y.hom))
        ((integralComponentAt
          (X := pullback (pullback.fst Y.hom T.hom ≫ Y.hom)
            (pullback.fst Z.hom T.hom ≫ Z.hom))
          (nativeExteriorPoint Y Z T w hw)).subschemeι ≫
            pullback.fst (pullback.fst Y.hom T.hom ≫ Y.hom)
              (pullback.fst Z.hom T.hom ≫ Z.hom)) =
      exteriorIncidenceProductSecond X Y Z T z w ≫
        (nativeExteriorSupportIso Y Z T w hw).hom :=
  exteriorIncidenceProductToNative_snd X Y Z T z w hz hw

/-- The literal product is a Cartesian square for the two actual native support projections. -/
theorem nativeExteriorIncidence_isPullback :
    IsPullback
      (exteriorIncidenceProductFirst X Y Z T z w ≫ (nativeExteriorSupportIso X Y T z hz).hom)
      (exteriorIncidenceProductSecond X Y Z T z w ≫ (nativeExteriorSupportIso Y Z T w hw).hom)
      ((integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom)
      ((integralComponentAt (nativeExteriorPoint Y Z T w hw)).subschemeι ≫
        pullback.fst (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom) :=
  IsPullback.of_iso_pullback
    ⟨by simpa only [Category.assoc, nativeExteriorSupportIso_hom_target,
      nativeExteriorSupportIso_hom_source] using exteriorIncidenceProduct_condition X Y Z T z w⟩
    (nativeExteriorIncidenceIso X Y Z T z w hz hw)
    (nativeExteriorIncidenceIso_hom_fst X Y Z T z w hz hw)
    (nativeExteriorIncidenceIso_hom_snd X Y Z T z w hz hw)

/-- Forgetting the parameter is the Cartesian base change of its structure map. -/
theorem nativeExteriorIncidenceOriginal_isPullback :
    IsPullback (nativeExteriorIncidenceOriginal X Y Z T z w hz hw)
      (nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ pullback.snd _ _)
      (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) T.hom :=
  IsPullback.of_iso_pullback
    ⟨by
      simp only [correspondenceIncidenceLeft, ← Category.assoc,
        nativeExteriorIncidenceOriginal_fst]
      simpa only [Category.assoc, exteriorSupportSourceProjection] using
        congrArg (fun f => nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ f)
          (pullback.condition
            (f := exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
            (g := T.hom))⟩
    (nativeExteriorIncidenceIso X Y Z T z w hz hw).symm
    (nativeExteriorIncidenceToProduct_fst X Y Z T z w hz hw)
    (nativeExteriorIncidenceToProduct_snd X Y Z T z w hz hw)

/-- The projection is smooth even if the original incidence is nonreduced. -/
@[stacks 01VB "Smooth base change applied to the actual full-incidence product projection"]
instance nativeExteriorIncidenceOriginal_smooth :
    Smooth (nativeExteriorIncidenceOriginal X Y Z T z w hz hw) :=
  MorphismProperty.of_isPullback
    (nativeExteriorIncidenceOriginal_isPullback X Y Z T z w hz hw).flip inferInstance

end Stacks.Chow

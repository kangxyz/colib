/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceProduct
public import Colib.AlgebraicGeometry.Correspondences.Exterior.PrimeSupport

/-!
# Coordinates of the actual native exterior incidence

Both support schemes are the native integral components at the actual exterior
prime points. Their existing support isomorphisms retain the ambient closed
immersions. The forward and backward maps below are actual pullback lifts.

Adapted from `motivic_source_a6805c4`, Exterior/Identity/Incidence.lean.
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

/-- An abbreviation for the existing native incidence, not a replacement support model. -/
abbrev nativeExteriorIncidence : Scheme.{u} :=
  correspondenceIncidence (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
    (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
    (nativeExteriorPoint Y Z T w hw)

/-- Map from the full literal product into the actual incidence of exterior primes. -/
def exteriorIncidenceProductToNative : exteriorIncidenceProduct X Y Z T z w ⟶
    nativeExteriorIncidence X Y Z T z w hz hw :=
  pullback.lift
    (exteriorIncidenceProductFirst X Y Z T z w ≫ (nativeExteriorSupportIso X Y T z hz).hom)
    (exteriorIncidenceProductSecond X Y Z T z w ≫ (nativeExteriorSupportIso Y Z T w hw).hom)
    (by
      simpa only [Category.assoc, nativeExteriorSupportIso_hom_target,
        nativeExteriorSupportIso_hom_source] using exteriorIncidenceProduct_condition X Y Z T z w)

@[reassoc (attr := simp)]
theorem exteriorIncidenceProductToNative_fst :
    exteriorIncidenceProductToNative X Y Z T z w hz hw ≫
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
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceProductToNative_snd :
    exteriorIncidenceProductToNative X Y Z T z w hz hw ≫
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
  pullback.lift_snd _ _ _

/-- The actual first exterior support coordinate. -/
abbrev nativeExteriorIncidenceFirst : nativeExteriorIncidence X Y Z T z w hz hw ⟶
    exteriorIdentitySupport X Y T (integralComponentAt z) :=
  pullback.fst _ _ ≫ (nativeExteriorSupportIso X Y T z hz).inv

/-- The actual second exterior support coordinate. -/
abbrev nativeExteriorIncidenceSecond : nativeExteriorIncidence X Y Z T z w hz hw ⟶
    exteriorIdentitySupport Y Z T (integralComponentAt w) :=
  pullback.snd _ _ ≫ (nativeExteriorSupportIso Y Z T w hw).inv

/-- The actual native incidence equation, transported through its support isomorphisms. -/
@[reassoc]
theorem nativeExteriorIncidence_condition :
    nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫
        exteriorIdentityTarget X Y T (integralComponentAt z) =
      nativeExteriorIncidenceSecond X Y Z T z w hz hw ≫
        exteriorIdentitySource Y Z T (integralComponentAt w) := by
  simpa only [nativeExteriorIncidenceFirst, nativeExteriorIncidenceSecond,
    Category.assoc, nativeExteriorSupportIso_inv_target, nativeExteriorSupportIso_inv_source]
    using (pullback.condition
      (f := (integralComponentAt (nativeExteriorPoint X Y T z hz)).subschemeι ≫
        pullback.snd (SmoothSite.product X T).hom (SmoothSite.product Y T).hom)
      (g := (integralComponentAt (nativeExteriorPoint Y Z T w hw)).subschemeι ≫
        pullback.fst (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom))

@[reassoc]
theorem nativeExteriorIncidence_middle :
    nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫
        pullback.fst (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
          T.hom ≫ exteriorSupportTargetProjection X Y (integralComponentAt z) =
      nativeExteriorIncidenceSecond X Y Z T z w hz hw ≫
        pullback.fst (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom)
          T.hom ≫ exteriorSupportSourceProjection Y Z (integralComponentAt w) := by
  simpa only [Category.assoc, exteriorIdentityTarget_fst, exteriorIdentitySource_fst] using
    congrArg (fun f => f ≫ pullback.fst Y.hom T.hom)
      (nativeExteriorIncidence_condition X Y Z T z w hz hw)

@[reassoc]
theorem nativeExteriorIncidence_parameter :
    nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫
        pullback.snd (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
          T.hom =
      nativeExteriorIncidenceSecond X Y Z T z w hz hw ≫
        pullback.snd (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom)
          T.hom := by
  simpa only [Category.assoc, exteriorIdentityTarget_snd, exteriorIdentitySource_snd] using
    congrArg (fun f => f ≫ pullback.snd Y.hom T.hom)
      (nativeExteriorIncidence_condition X Y Z T z w hz hw)

/-- Forgetting the parameter lands in the full original incidence scheme. -/
def nativeExteriorIncidenceOriginal : nativeExteriorIncidence X Y Z T z w hz hw ⟶
    correspondenceIncidence X.hom Y.hom Z.hom z w :=
  pullback.lift
    (nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ pullback.fst _ _)
    (nativeExteriorIncidenceSecond X Y Z T z w hz hw ≫ pullback.fst _ _)
    (by simpa only [Category.assoc] using nativeExteriorIncidence_middle X Y Z T z w hz hw)

@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceOriginal_fst :
    nativeExteriorIncidenceOriginal X Y Z T z w hz hw ≫ pullback.fst _ _ =
      nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceOriginal_snd :
    nativeExteriorIncidenceOriginal X Y Z T z w hz hw ≫ pullback.snd _ _ =
      nativeExteriorIncidenceSecond X Y Z T z w hz hw ≫ pullback.fst _ _ :=
  pullback.lift_snd _ _ _

/-- Recover the original incidence and its shared parameter. -/
def nativeExteriorIncidenceToProduct : nativeExteriorIncidence X Y Z T z w hz hw ⟶
    exteriorIncidenceProduct X Y Z T z w :=
  pullback.lift (nativeExteriorIncidenceOriginal X Y Z T z w hz hw)
    (nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ pullback.snd _ _) (by
      simp only [correspondenceIncidenceLeft, ← Category.assoc,
        nativeExteriorIncidenceOriginal_fst]
      simpa only [Category.assoc, exteriorSupportSourceProjection] using
        congrArg (fun f => nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ f)
          (pullback.condition
            (f := exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
            (g := T.hom)))

@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceToProduct_fst :
    nativeExteriorIncidenceToProduct X Y Z T z w hz hw ≫ pullback.fst _ _ =
      nativeExteriorIncidenceOriginal X Y Z T z w hz hw :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceToProduct_snd :
    nativeExteriorIncidenceToProduct X Y Z T z w hz hw ≫ pullback.snd _ _ =
      nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ pullback.snd _ _ :=
  pullback.lift_snd _ _ _

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Incidence.lean:98-241"
  "adaptation" "Actual native exterior-prime incidence and its full original incidence coordinate"]
  exteriorIncidenceProductToNative nativeExteriorIncidenceOriginal nativeExteriorIncidenceToProduct

end Stacks.Chow

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.LineZeroCoordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComplement
public import Colib.AlgebraicGeometry.ProjectiveLine.Neighborhood.NativeMarkedMaps

/-! # The entire polynomial puncture is the actual native torus over its base

Two full zero squares identify the open complements. The resulting comparison
is an isomorphism because the whole-line comparison is an isomorphism. This
keeps the positive native open and the original polynomial coefficient map.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The original whole D(X), regarded as an open of the literal polynomial line. -/
abbrev polynomialPunctureInclusion :
    (opensFunctor (lineSite (k := k) (R := R))).obj
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)) ⟶
        lineSite (k := k) (R := R) :=
  _root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion (lineSite (k := k) (R := R))
    (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))

instance : IsOpenImmersion (polynomialPunctureInclusion (k := k) (R := R)).left :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι
    (X := Spec (CommRingCat.of (Polynomial R)))
    (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))))

/-- Only the base is restricted: no smaller open of D(X) is selected. -/
abbrev wholeBasePuncture (V : (Spec (.of R)).Opens) :=
  etalePullback (polynomialPunctureInclusion (k := k) (R := R))
    (_root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion
      (lineSite (k := k) (R := R)) (polynomialProjection (.of R) ⁻¹ᵁ V))

/-- The full original zero is the exact complement of this puncture. -/
theorem range_lineZero :
    Set.range (lineZero (k := k) (R := R)).left =
      (Set.range (polynomialPunctureInclusion (k := k) (R := R)).left)ᶜ := by
  classical
  let U : (Spec (CommRingCat.of (Polynomial R))).Opens :=
    PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)
  change Set.range (lineZero (k := k) (R := R)).left = (Set.range U.ι)ᶜ
  rw [Scheme.Opens.range_ι]
  ext x
  change x ∈ Set.range (lineZero (k := k) (R := R)).left ↔
    ¬ Polynomial.X ∉ x.asIdeal
  rw [not_not]
  exact RelativeCurve.NativeProjectiveLine.mem_range_evalZero_iff R x

/-- Both zero squares construct the actual whole-torus comparison. -/
theorem exists_wholeBasePuncture_comparison (V : (Spec (.of R)).Opens) :
    ∃ t : wholeBasePuncture (k := k) V ⟶
        torusCylinder.obj ((opensFunctor (affineSite k R)).obj V),
      IsPullback t
        (etalePullbackSnd (polynomialPunctureInclusion (k := k) (R := R))
          (_root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion _ _))
        (Contraction.openInclusion.app ((opensFunctor (affineSite k R)).obj V))
        (lineBaseOpenCylinderIso (k := k) V).hom := by
  have H : IsPullback (lineBaseOpenZero (k := k) V).left (𝟙 _)
      (lineBaseOpenCylinderIso (k := k) V).hom.left
      (nativeAffineSection (.of k) ((opensFunctor (affineSite k R)).obj V) 0).left :=
    IsPullback.of_vert_isIso_mono
      ⟨(congrArg (fun f => f.left) (lineBaseOpenZero_cylinder (k := k) V)).trans
        (Category.id_comp _).symm⟩
  exact (exists_native_cartier_puncture_comparison (.of k)
    (polynomialPunctureInclusion (k := k) (R := R))
    (_root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion _ _)
    (lineBaseOpenCylinderIso (k := k) V).hom (lineBaseOpenZero (k := k) V)
    (lineZero (k := k) (R := R)).left V.ι
    (lineBaseOpenZero_isPullback (k := k) V) H (range_lineZero (k := k) (R := R))).2

/-- The same map chosen by the exact complement construction. -/
def wholeBasePunctureToTorus (V : (Spec (.of R)).Opens) :
    wholeBasePuncture (k := k) V ⟶
      torusCylinder.obj ((opensFunctor (affineSite k R)).obj V) :=
  (exists_wholeBasePuncture_comparison (k := k) V).choose

theorem wholeBasePunctureToTorus_isPullback (V : (Spec (.of R)).Opens) :
    IsPullback (wholeBasePunctureToTorus (k := k) V)
      (etalePullbackSnd (polynomialPunctureInclusion (k := k) (R := R))
        (_root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion _ _))
      (Contraction.openInclusion.app ((opensFunctor (affineSite k R)).obj V))
      (lineBaseOpenCylinderIso (k := k) V).hom :=
  (exists_wholeBasePuncture_comparison (k := k) V).choose_spec

instance (V : (Spec (.of R)).Opens) : IsIso (wholeBasePunctureToTorus (k := k) V) :=
  (wholeBasePunctureToTorus_isPullback (k := k) V).isIso_fst_of_isIso

/-- This is the whole native multiplicative cylinder, not a dense smaller open. -/
def wholeBasePunctureTorusIso (V : (Spec (.of R)).Opens) :
    wholeBasePuncture (k := k) V ≅
      torusCylinder.obj ((opensFunctor (affineSite k R)).obj V) :=
  asIso (wholeBasePunctureToTorus (k := k) V)

/-- The comparison preserves the literal positive native inclusion. -/
@[reassoc] theorem wholeBasePunctureTorusIso_open (V : (Spec (.of R)).Opens) :
    (wholeBasePunctureTorusIso (k := k) V).hom ≫
      Contraction.openInclusion.app ((opensFunctor (affineSite k R)).obj V) =
    etalePullbackSnd (polynomialPunctureInclusion (k := k) (R := R))
      (_root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion _ _) ≫
        (lineBaseOpenCylinderIso (k := k) V).hom :=
  (wholeBasePunctureToTorus_isPullback (k := k) V).w

/-- Its affine ambient map is the original whole polynomial base restriction. -/
@[reassoc] theorem wholeBasePunctureTorusIso_original (V : (Spec (.of R)).Opens) :
    (wholeBasePunctureTorusIso (k := k) V).hom ≫
      Contraction.openInclusion.app ((opensFunctor (affineSite k R)).obj V) ≫
        affineLineCylinder.map
          (_root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion (affineSite k R) V) =
    etalePullbackFst (polynomialPunctureInclusion (k := k) (R := R))
      (_root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion _ _) ≫
        polynomialPunctureInclusion ≫ (lineCylinderIso (k := k) (R := R)).hom := by
  let p := polynomialPunctureInclusion (k := k) (R := R)
  let v := _root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion
    (lineSite (k := k) (R := R)) (polynomialProjection (.of R) ⁻¹ᵁ V)
  let m := affineLineCylinder.map
    (_root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion (affineSite k R) V)
  let l := (lineCylinderIso (k := k) (R := R)).hom
  have h := (etalePullbackCone p v).condition
  calc
    _ = etalePullbackSnd p v ≫ (lineBaseOpenCylinderIso (k := k) V).hom ≫ m :=
      wholeBasePunctureTorusIso_open_assoc (k := k) V m
    _ = etalePullbackSnd p v ≫ v ≫ l :=
      congrArg (fun f => etalePullbackSnd p v ≫ f) (lineBaseOpenCylinderIso_comp (k := k) V)
    _ = (etalePullbackSnd p v ≫ v) ≫ l := (Category.assoc _ _ _).symm
    _ = (etalePullbackFst p v ≫ p) ≫ l := congrArg (fun f => f ≫ l) h.symm
    _ = _ := Category.assoc _ _ _

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

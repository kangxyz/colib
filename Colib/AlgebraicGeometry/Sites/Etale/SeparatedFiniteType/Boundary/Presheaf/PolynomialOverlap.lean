/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.PuncturedCoordinates
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.Geometry
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineSectionNaturality
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-! # The original polynomial overlap restricts the actual boundary section -/

/-! Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/PolynomialOverlap.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
The group objects, closed markings, and overlap map are those of the
original beta-minus-alpha identity. -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.PolynomialOpenQuotient
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  {R : Type u} [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  (v : SmoothSite.affineSite k R ⟶ X)

/-- The original polynomial puncture maps to the original torus, with both coordinates retained. -/
def polynomialPunctureToTorus :
    SmoothSite.openSite (k := k) (Polynomial.X : Polynomial R) ⟶
      SmoothSite.Contraction.torusCylinder.obj X :=
  (SmoothSite.puncturedProductIso (k := k) (R := R)).hom ≫
    SmoothSite.Contraction.torusCylinder.map v

/-- This is the unchanged original puncture inclusion over the original base. -/
@[reassoc] theorem polynomialPunctureToTorus_open :
    polynomialPunctureToTorus X v ≫ SmoothSite.Contraction.openInclusion.app X =
      PolynomialOpenQuotient.SmoothSite.openInclusion (k := k) (Polynomial.X : Polynomial R) ≫
        (AffineCoordinates.lineCylinderIso (k := k) (R := R)).hom ≫
          SmoothSite.Contraction.affineLineCylinder.map v := by
  rw [polynomialPunctureToTorus, Category.assoc,
    SmoothSite.Contraction.openInclusion.naturality, ← Category.assoc,
    SmoothSite.puncturedProductIso_open, Category.assoc]
  rfl

variable (W : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left)
  {Y : SmoothSite (Spec (.of k))}
  (p : Y ⟶ SmoothSite.lineSite (k := k) (R := R)) [Etale p.left]
  (e : Y ⟶ (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).obj W)
  (hp : p ≫ (AffineCoordinates.lineCylinderIso (k := k) (R := R)).hom ≫
    SmoothSite.Contraction.affineLineCylinder.map v = e ≫ toBase
(SmoothSite.Contraction.affineLineCylinder.obj X) W)

include hp in
/-- The actual original overlap maps to the actual original punctured small-site
neighborhood, before restricting any section of P. -/
def polynomialOverlapToPunctured :
    SmoothSite.etalePullback p
      (PolynomialOpenQuotient.SmoothSite.openInclusion (k := k) (Polynomial.X : Polynomial R)) ⟶
    (toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).obj
      ((baseChange (SmoothSite.Contraction.openInclusion.app X).left).obj W) := by
  let a := PolynomialOpenQuotient.SmoothSite.openInclusion (k := k) (Polynomial.X : Polynomial R)
  let l := SmoothSite.etalePullbackFst p a
  let n := SmoothSite.etalePullbackSnd p a
  have hc : (l ≫ e) ≫ toBase (SmoothSite.Contraction.affineLineCylinder.obj X) W =
      (n ≫ polynomialPunctureToTorus X v) ≫ SmoothSite.Contraction.openInclusion.app X := by
    have hPB := (SmoothSite.etalePullbackCone p a).condition
    change l ≫ p = n ≫ a at hPB
    rw [Category.assoc, ← hp, ← Category.assoc l p, hPB]
    simp only [Category.assoc, polynomialPunctureToTorus_open, a]
  exact SmoothSite.homMk
    (pullback.lift (l.left ≫ e.left) (n.left ≫ (polynomialPunctureToTorus X v).left)
      (congrArg (fun f => f.left) hc)) (by
        change pullback.lift _ _ _ ≫
          (pullback.snd W.hom (SmoothSite.Contraction.openInclusion.app X).left ≫
            (SmoothSite.Contraction.torusCylinder.obj X).hom) = _
        rw [pullback.lift_snd_assoc]
        exact MorphismProperty.Over.w (n ≫ polynomialPunctureToTorus X v))

/-- Original ambient projection of the original overlap restriction. -/
@[reassoc] theorem polynomialOverlapToPunctured_fst :
    (polynomialOverlapToPunctured X v W p e hp).left ≫
      pullback.fst W.hom (SmoothSite.Contraction.openInclusion.app X).left =
    (SmoothSite.etalePullbackFst p
      (PolynomialOpenQuotient.SmoothSite.openInclusion (k := k) (Polynomial.X : Polynomial R))).left
          ≫
        e.left := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- Original torus projection of that same overlap restriction. -/
@[reassoc] theorem polynomialOverlapToPunctured_snd :
    (polynomialOverlapToPunctured X v W p e hp).left ≫
      pullback.snd W.hom (SmoothSite.Contraction.openInclusion.app X).left =
    (SmoothSite.etalePullbackSnd p
      (PolynomialOpenQuotient.SmoothSite.openInclusion (k := k) (Polynomial.X : Polynomial R))).left
          ≫
        (polynomialPunctureToTorus X v).left := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf

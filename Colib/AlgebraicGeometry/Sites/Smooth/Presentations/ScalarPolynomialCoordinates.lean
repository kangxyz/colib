/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.ScalarCoordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.PolynomialAffineCoordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.LineZeroCoordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.BaseChange.FieldBaseChangeA1

/-! # Scalar polynomial coordinates preserve the whole original zero section

The two coordinate models are related through the native scalar cylinder. No
new polynomial algebra, zero scheme, or pointwise replacement is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

variable (k R L : Type u) [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L] [Algebra.Smooth k R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The smoothness instance used in this module. -/
local instance scalarPolynomialCoordinatesSmooth1 : Algebra.Smooth L (R ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)

/-- The smoothness instance used in this module. -/
local instance scalarPolynomialCoordinatesSmooth2 : Algebra.Smooth k (Polynomial R) := by
  let : Algebra.Smooth R (Polynomial R) := {}
  exact Algebra.Smooth.comp k R (Polynomial R)

/-- The smoothness instance used in this module. -/
local instance scalarPolynomialCoordinatesSmooth3 : Algebra.Smooth L ((Polynomial R) ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L (Polynomial R))

/-- Scalar extension of the literal relative polynomial line, through its native
cylinder and the canonical tensor coordinates on the base. -/
def scalarLineIso :
    (fieldBaseChange (algebraMap k L)).obj (lineSite (k := k) (R := R)) ≅
      lineSite (k := L) (R := R ⊗[k] L) :=
  (fieldBaseChange (algebraMap k L)).mapIso lineCylinderIso ≪≫
    fieldBaseChangeA1Iso (affineSite k R) ≪≫
      cylinderIso (affineScalarIso k R L) ≪≫ lineCylinderIso.symm

/-- The actual tensor algebra of the original polynomial ring is identified with
the polynomial line over the actual scalar base, not a replacement presentation. -/
def tensorPolynomialLineIso :
    affineSite L ((Polynomial R) ⊗[k] L) ≅ lineSite (k := L) (R := R ⊗[k] L) :=
  (affineScalarIso k (Polynomial R) L).symm ≪≫
    (fieldBaseChange (algebraMap k L)).mapIso
      (polynomialAffineIso k R).symm ≪≫ scalarLineIso k R L

/-- The scalar polynomial coordinate comparison preserves the entire original
zero morphism, before any closed point is selected. -/
@[reassoc]
theorem scalarLineIso_zero :
    (fieldBaseChange (algebraMap k L)).map
        (nativeAffineSection (.of k) (affineSite k R) 0 ≫
          (lineCylinderIso (k := k) (R := R)).inv) ≫
      (scalarLineIso k R L).hom =
    (affineScalarIso k R L).hom ≫
      nativeAffineSection (.of L) (affineSite L (R ⊗[k] L)) 0 ≫
        (lineCylinderIso (k := L) (R := R ⊗[k] L)).inv := by
  simp only [scalarLineIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  have hz : (fieldBaseChange (algebraMap k L)).map
      (nativeAffineSection (.of k) (affineSite k R) 0) ≫
        (fieldBaseChangeA1Iso (L := L) (affineSite k R)).hom =
      nativeAffineSection (.of L)
        ((fieldBaseChange (algebraMap k L)).obj (affineSite k R)) 0 :=
    fieldBaseChangeA1Iso_zero (L := L) (affineSite k R)
  rw [← Category.assoc, ← Category.assoc, hz]
  change (nativeAffineSection (.of L) _ 0 ≫
      affineLineCylinder.map (affineScalarIso k R L).hom) ≫ _ = _
  rw [nativeAffineSection_naturality, Category.assoc]

/-- A section on the whole original base, rather than merely its selected
point, gives the whole scalar zero lift into the native scalar étale source. -/
@[reassoc]
theorem scalarLineIso_wholeSection
    {Y : SmoothSite (Spec (.of k))} (p : Y ⟶ lineSite (k := k) (R := R))
    (s₀ : affineSite k R ⟶ Y)
    (hs₀ : s₀ ≫ p = nativeAffineSection (.of k) (affineSite k R) 0 ≫
      (lineCylinderIso (k := k) (R := R)).inv) :
    (affineScalarIso k R L).inv ≫
      (fieldBaseChange (algebraMap k L)).map s₀ ≫
        (fieldBaseChange (algebraMap k L)).map p ≫
          (scalarLineIso k R L).hom =
      nativeAffineSection (.of L) (affineSite L (R ⊗[k] L)) 0 ≫
        (lineCylinderIso (k := L) (R := R ⊗[k] L)).inv := by
  rw [← Functor.map_comp_assoc, hs₀, scalarLineIso_zero]
  simp

/-- The source of the preceding identity is the literal polynomial evaluation
map, including its complete scheme structure. -/
theorem polynomial_zero_left :
    (nativeAffineSection (.of k) (affineSite k R) 0 ≫
      (lineCylinderIso (k := k) (R := R)).inv).left =
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) := by
  have hz : nativeAffineSection (.of k) (affineSite k R) 0 ≫
      (lineCylinderIso (k := k) (R := R)).inv = lineZero := by
    rw [← lineZero_cylinder, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg (fun f => f.left) hz

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

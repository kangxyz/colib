/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Moving.PrincipalOrder
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedFamilyRestriction
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.ParameterGeometry

/-! # The actual polynomial family of a boundary unit

The numerator is the literal interpolation between one and the original
unit. Its signed principal correspondence is formed over the original
polynomial cylinder with the full omitted boundary retained.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/Moving/Polynomial/`
`PrincipalFamilyPointCycle.lean` at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Cor.PrincipalOrder

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
open _root_.AlgebraicGeometry.PrincipalFamilyUnitOpen hiding
  parameterSpace projection parameter endpoint

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
  {C V B : Scheme.{u}} [IsIntegral C] [IsNoetherian C] [V.IsQuasiAffine]
  (q : C ⟶ X.left) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  (W : C.Opens) (r : Γ(C, W)) (b : B ⟶ W.toScheme) [Nonempty B]
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ W.ι)) (hb : b.appTop (W.topIso.inv r) = 1)
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

/-- The signed principal cycle of the actual interpolated unit defines a
finite correspondence on the whole original polynomial cylinder. -/
def familyCorrespondence : Cor.mk (SmoothSite.product X (polynomialAffineLine (.of k))) ⟶
    Cor.mk Y := by
  let L := SmoothSite.product X (polynomialAffineLine (.of k))
  let t := q ≫ X.hom
  let q' : parameterSpace t ⟶ L.left := parameterMap X.hom q
  let j' := parameterMap t j
  let : IsProper q' := MorphismProperty.of_isPullback
    (parameterMap_isPullback X.hom q) inferInstance
  let : IsOpenImmersion j' := inferInstanceAs (IsOpenImmersion (parameterMap t j))
  let : (parameterSpace (j ≫ t)).IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom
    (projection (j ≫ t))
  let hAffine : IsAffine (parameterSpace X.hom) :=
    isAffine_of_isAffineHom (X := parameterSpace X.hom) (Y := X.left) (projection X.hom)
  let : IsAffine L.left := hAffine
  let : SmoothOfRelativeDimension 1 (j' ≫ q') := by
    change SmoothOfRelativeDimension 1 (parameterMap (q ≫ X.hom) j ≫ parameterMap X.hom q)
    rw [parameterMap_comp]
    exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (parameterMap_isPullback X.hom (j ≫ q)) inferInstance
  let f := W.topIso.inv r
  let U := ambientUnitOpen t W.ι f
  let : Nonempty U := nonempty_ambientUnitOpen_of_boundary t W.ι b f hb
  let s := ambientUnitSection t W.ι f
  have hU := complement_subset_ambientUnitOpen t j W.ι b hcover f hb
  rw [lineMap_eq_parameterMap] at hU
  let g' := projection (j ≫ t) ≫ g
  have hg : j' ≫ q' ≫ L.hom = g' ≫ Y.hom := by
    change parameterMap t j ≫ parameterMap X.hom q ≫ projection X.hom ≫ X.hom = _
    simp only [parameterMap_projection_assoc, Category.assoc, g', t, hbase]
  exact correspondence q' j' U hU s (isUnit_ambientUnitSection t W.ι f) g' hg

end AlgebraicGeometry.Cor.PrincipalOrder

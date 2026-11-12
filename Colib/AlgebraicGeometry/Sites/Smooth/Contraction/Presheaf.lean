/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# The geometric contraction of an ordinary abelian presheaf

This is the actual cokernel of restriction from the native affine-line cylinder
to its positive Laurent open. Its component groups are the literal quotients.
Constants factor through that restriction and split under the actual unit section.

The construction is the ordinary-presheaf part of
`Motivic/Transfers/Presheaf/Contraction.lean` at `motivic_source_a6805c4`.
There is no assertion that the quotient carries all finite-correspondence
transfers, is a sheaf, or satisfies strict A¹-invariance.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable {S : Scheme.{u}} (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{v})

/-- Coefficients on the actual relative product with a parameter. -/
abbrev parameterSections (T : SmoothSite S) : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{v} :=
  (parameterProduct T).op ⋙ P

/-- The ordinary coefficient restriction along the actual Laurent open. -/
def restriction : parameterSections P (additiveGroupObject S) ⟶
    parameterSections P (multiplicativeGroupObject S) :=
  Functor.whiskerRight (NatTrans.op openInclusion) P

@[simp]
theorem restriction_app (X : SmoothSite S) :
    (restriction P).app (op X) = P.map (openInclusion.app X).op := rfl

/-- The quotient by the actual affine-line restriction, in the ordinary presheaf category. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/Contraction.lean:55-78"
  "adaptation" "The geometric ordinary-presheaf quotient, before extending signed transfers"]
def presheaf : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{v} := cokernel (restriction P)

/-- The actual quotient map from Laurent-cylinder sections. -/
def quotient : parameterSections P (multiplicativeGroupObject S) ⟶ presheaf P :=
  cokernel.π (restriction P)

@[reassoc (attr := simp)]
theorem restriction_quotient : restriction P ≫ quotient P = 0 :=
  cokernel.condition _

/-- Pullback of coefficients along the genuine parameter projection. -/
def constant (T : SmoothSite S) : P ⟶ parameterSections P T where
  app X := P.map ((projection T).app X.unop).op
  naturality X Y f := by
    change P.map f ≫ P.map (productFst Y.unop T).op =
      P.map (productFst X.unop T).op ≫ P.map (productMap f.unop (𝟙 T)).op
    rw [← P.map_comp, ← P.map_comp]
    congr 1
    exact congrArg Quiver.Hom.op (productMap_fst f.unop (𝟙 T)).symm

/-- Evaluation at the actual unit section, with no homotopy-invariance hypothesis. -/
def unit : parameterSections P (multiplicativeGroupObject S) ⟶ P where
  app X := P.map (unitSection.app X.unop).op
  naturality X Y f := by
    change P.map (productMap f.unop (𝟙 (multiplicativeGroupObject S))).op ≫
      P.map (unitSection.app Y.unop).op =
      P.map (unitSection.app X.unop).op ≫ P.map f
    rw [← P.map_comp, ← P.map_comp]
    congr 1
    exact congrArg Quiver.Hom.op (unitSection.naturality f.unop).symm

@[reassoc (attr := simp)]
theorem constant_unit : constant P (multiplicativeGroupObject S) ≫ unit P = 𝟙 P := by
  apply NatTrans.ext
  funext X
  change P.map ((projection (multiplicativeGroupObject S)).app X.unop).op ≫
    P.map (unitSection.app X.unop).op = 𝟙 _
  rw [← P.map_comp, ← op_comp, unitSection_projection]
  change P.map (𝟙 X) = 𝟙 (P.obj X)
  exact P.map_id X

/-- Constants on the punctured cylinder are restrictions of actual affine-line constants. -/
@[reassoc (attr := simp)]
theorem constant_restriction : constant P (additiveGroupObject S) ≫ restriction P =
    constant P (multiplicativeGroupObject S) := by
  apply NatTrans.ext
  funext X
  change P.map ((projection (additiveGroupObject S)).app X.unop).op ≫
    P.map (openInclusion.app X.unop).op =
      P.map ((projection (multiplicativeGroupObject S)).app X.unop).op
  rw [← P.map_comp, ← op_comp, openInclusion_projection]

/-- The actual quotient kills the constant summand, without an invariance assumption. -/
@[reassoc (attr := simp)]
theorem constant_quotient : constant P (multiplicativeGroupObject S) ≫ quotient P = 0 := by
  rw [← constant_restriction P, Category.assoc, restriction_quotient, comp_zero]

/-- Every quotient section has a genuine Laurent-cylinder representative. -/
theorem quotient_surjective (X : SmoothSite S) :
    Function.Surjective ((quotient P).app (op X)) := by
  change Function.Surjective ((cokernel.π (restriction P)).app (op X))
  exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance

/-- The objectwise quotient uses the range of the literal open-restriction map. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/Contraction.lean:118-125"
  "adaptation" "Component quotient for the actual native Laurent restriction"]
def sectionsIsoQuotient (X : SmoothSite S) :
    (presheaf P).obj (op X) ≅ AddCommGrpCat.of
      (P.obj (op (torusCylinder.obj X)) ⧸ (P.map (openInclusion.app X).op).hom.range) :=
  PreservesCokernel.iso ((CategoryTheory.evaluation (SmoothSite S)ᵒᵖ AddCommGrpCat).obj (op X))
      (restriction P) ≪≫ AddCommGrpCat.cokernelIsoQuotient ((restriction P).app (op X))

/-- The comparison identifies the actual quotient map, not just its target object. -/
@[reassoc (attr := simp)]
theorem quotient_sectionsIsoQuotient_hom (X : SmoothSite S) :
    (quotient P).app (op X) ≫ (sectionsIsoQuotient P X).hom =
      AddCommGrpCat.ofHom
        (QuotientAddGroup.mk' (P.map (openInclusion.app X).op).hom.range) := by
  let E := (CategoryTheory.evaluation (SmoothSite S)ᵒᵖ AddCommGrpCat).obj (op X)
  change E.map (cokernel.π (restriction P)) ≫
    ((PreservesCokernel.iso E (restriction P)).hom ≫
      (AddCommGrpCat.cokernelIsoQuotient ((restriction P).app (op X))).hom) = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

/-- Source restriction acts on represented classes by the literal product map. -/
theorem map_quotient_apply {X Y : SmoothSite S} (f : X ⟶ Y)
    (s : P.obj (op (torusCylinder.obj Y))) :
    (presheaf P).map f.op ((quotient P).app (op Y) s) =
      (quotient P).app (op X) (P.map (productMap f (𝟙 (multiplicativeGroupObject S))).op s) :=
  (NatTrans.naturality_apply (quotient P) f.op s).symm

end AlgebraicGeometry.Scheme.SmoothSite.Contraction

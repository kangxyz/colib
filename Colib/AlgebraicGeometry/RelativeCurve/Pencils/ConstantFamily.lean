/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedProductFamily

/-!
# The actual constant whole zero family is finite flat by base change

The constant polynomial pencil of a section has exactly the inverse-image zero
ideal under the parameter projection. Its full zero scheme, including nilpotents,
is identified with the actual pullback. Pasting the parameter Cartesian square
then derives finite flatness over the original source cylinder from finite
flatness of the original pole. No constant-family finiteness premise is added.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.PolynomialSectionPencil

variable {R : Type u} [CommRing R] {X C : Scheme.{u}} (b : X ⟶ Spec (.of R))
  (p : C ⟶ X) (L : C.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

omit [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L] in
@[simp]
theorem familySection_constant :
    familySection (p ≫ b) L s s = pullbackGlobalSections (projection (p ≫ b)) L s := by
  simp only [familySection, sub_self, smul_zero, add_zero]

/-- The whole constant family has the actual pullback zero ideal. -/
theorem familyZero_constant :
    familyZero (p ≫ b) L s s = (zeroScheme C L s).comap (projection (p ≫ b)) := by
  rw [familyZero, familySection_constant, zeroScheme_pullback]

/-- The unreduced constant support is the literal pullback of the original pole. -/
def constantFamilySupportIso :
    (familyZero (p ≫ b) L s s).subscheme ≅
      pullback (projection (p ≫ b)) (zeroScheme C L s).subschemeι :=
  eqToIso (congrArg IdealSheafData.subscheme (familyZero_constant b p L s)) ≪≫
    (zeroScheme C L s).comapIso (projection (p ≫ b))

private theorem subscheme_transport_inclusion {Y : Scheme.{u}}
    {I J : Y.IdealSheafData} (h : I = J) :
    eqToHom (congrArg IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

/-- The comparison preserves the actual total-space inclusion. -/
@[reassoc]
theorem constantFamilySupportIso_hom_fst :
    (constantFamilySupportIso b p L s).hom ≫
      pullback.fst (projection (p ≫ b)) (zeroScheme C L s).subschemeι =
        (familyZero (p ≫ b) L s s).subschemeι := by
  simp only [constantFamilySupportIso, Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [IdealSheafData.comapIso_hom_fst]
  exact subscheme_transport_inclusion (familyZero_constant b p L s)

/-- Original finite poles give finite whole constant polynomial families. -/
theorem isFinite_constantFamilySource [IsFinite ((zeroScheme C L s).subschemeι ≫ p)] :
    IsFinite (familySource b p L s s) := by
  have H := ((IsPullback.of_hasPullback (projection (p ≫ b))
    (zeroScheme C L s).subschemeι).flip).paste_vert (parameterMap_isPullback b p)
  have : IsFinite (pullback.fst (projection (p ≫ b)) (zeroScheme C L s).subschemeι ≫
      parameterMap b p) := MorphismProperty.of_isPullback H inferInstance
  change IsFinite ((familyZero (p ≫ b) L s s).subschemeι ≫ parameterMap b p)
  rw [← constantFamilySupportIso_hom_fst b p L s, Category.assoc]
  infer_instance

/-- Original flat poles give flat whole constant polynomial families. -/
theorem flat_constantFamilySource [Flat ((zeroScheme C L s).subschemeι ≫ p)] :
    Flat (familySource b p L s s) := by
  have H := ((IsPullback.of_hasPullback (projection (p ≫ b))
    (zeroScheme C L s).subschemeι).flip).paste_vert (parameterMap_isPullback b p)
  have : Flat (pullback.fst (projection (p ≫ b)) (zeroScheme C L s).subschemeι ≫
      parameterMap b p) := MorphismProperty.of_isPullback H inferInstance
  change Flat ((familyZero (p ≫ b) L s s).subschemeι ≫ parameterMap b p)
  rw [← constantFamilySupportIso_hom_fst b p L s, Category.assoc]
  infer_instance

end AlgebraicGeometry.Scheme.PolynomialSectionPencil

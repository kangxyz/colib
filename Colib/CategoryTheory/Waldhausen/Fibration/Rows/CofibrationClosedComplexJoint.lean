/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cylinder.CofibrationClosed
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.SecondEndpoint

/-! # Actual ambient-monomorphism joint data for nested weak equivalences

Adapted from `Quillen/Waldhausen/Fibration/Rows/ComplexRelativeJoint.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The fine structure here is the existing
cofibration-closed full subcategory of `complexes A`, not `complexSubcategory P`.
No shift closure, fibration conclusion, or exactness assumption is supplied.
Source-only draft; no compilation claim.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open CategoryTheory.ExactCategory CochainComplex.SplitFactorization
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.Waldhausen.Fibration
open CofibrationClosedCylinder
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (H : CofibrationClosedSubcategory.Closed (complexes A) P)
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (N : NestedWeakEquivalences (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H))

/-- Constructed joint data for the original ambient-monomorphism model. -/
def cofibrationClosedComplexJointData : RowFactorization.JointData N where
  joint := jointFunctor P H hcone
  exact := jointFunctor_exact P H hcone
  inl := subcategoryJointSourceInl P
  inr := subcategoryJointSourceInr P
  coproduct := subcategoryJointSourceCofanIsColimit P
  projection := CofibrationClosedCylinder.projection P H hcone
  factorization f := by
    apply ObjectProperty.hom_ext
    change biprod.inl ≫ jointInclusion f.hom.hom ≫
      CochainComplex.SplitFactorization.projection f.hom.hom = _
    rw [← Category.assoc, jointInclusion, biprod.inl_desc]
    exact inclusion_projection f.hom.hom
  weak f := N.le_weq _ (projection_quasiIso f.hom.hom)

/-- The target endpoint is a section of the unchanged projection. -/
theorem cofibrationClosedComplexJointData_secondEndpointSection :
    RowFactorization.SecondEndpointSection N
      (cofibrationClosedComplexJointData P H hcone N) := by
  intro f
  apply ObjectProperty.hom_ext
  change biprod.inr ≫ jointInclusion f.hom.hom ≫
    CochainComplex.SplitFactorization.projection f.hom.hom = 𝟙 _
  rw [← Category.assoc, jointInclusion, biprod.inr_desc]
  exact biprod.inr_snd

/-- The induced row factorization uses the unchanged original quotient-row model. -/
def cofibrationClosedComplexRowFactorization (n : SimplexCategory) :
    FunctorialFactorization (RowWeakEquivalences.coarseStructure N n) :=
  RowFactorization.factorization N (cofibrationClosedComplexJointData P H hcone N) n

@[simp] theorem cofibrationClosedComplexRowFactorization_inclusion_component
    {n : SimplexCategory} (f : Arrow (QuotientRows.Obj
      (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H) n)) (p : Interval n) :
    (((cofibrationClosedComplexRowFactorization P H hcone N n).inclusion.app f).hom.app p).hom =
      CochainComplex.SplitFactorization.inclusion (f.hom.hom.app p).hom := by
  change biprod.inl ≫ jointInclusion (f.hom.hom.app p).hom = _
  exact biprod.inl_desc _ _

@[simp] theorem cofibrationClosedComplexRowFactorization_projection_component
    {n : SimplexCategory} (f : Arrow (QuotientRows.Obj
      (CofibrationClosedSubcategory.waldhausenStructure (complexes A) P H) n)) (p : Interval n) :
    (((cofibrationClosedComplexRowFactorization P H hcone N n).projection.app f).hom.app p).hom =
      CochainComplex.SplitFactorization.projection (f.hom.hom.app p).hom := rfl

end CategoryTheory.Waldhausen.Fibration

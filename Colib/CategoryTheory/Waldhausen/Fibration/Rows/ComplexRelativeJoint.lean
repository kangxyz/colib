/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.SecondEndpoint
public import Colib.CategoryTheory.Waldhausen.Cylinder.JointExact
public import Colib.CategoryTheory.Waldhausen.Fibration.ComplexChainReplacement

/-!
# Genuine complex joint cylinders for a nested relative weak class

The fine structure here has quasi-isomorphisms as weak equivalences, unlike
`complexJointData`, whose fine structure has isomorphisms. The actual existing
joint functor is quasi-exact. Its original projection is coarse-weak by the
inclusion of the fine weak class. The original second endpoint is a section
of that projection. No approximation or localization conclusion is assumed.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Fibration/Rows/ComplexRelativeJoint.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual complexes, maps and independent universes are retained. -/

@[expose] public section

open CategoryTheory.Waldhausen.SplitFactorization


open CategoryTheory.ExactCategory


noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration
open SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))
  (N : NestedWeakEquivalences (complexSubcategory P))

/-- The actual quasi-exact joint cylinder for any coarse class containing quasi-isomorphisms. -/
def complexJointDataOfNested : RowFactorization.JointData N where
  joint := subcategoryJointFunctor P hcone hshift
  exact := subcategoryJointFunctor_quasiExact P hcone hshift
  inl := subcategoryJointSourceInl P
  inr := subcategoryJointSourceInr P
  coproduct := subcategoryJointSourceCofanIsColimit P
  projection := (complexSubcategoryFactorization P hcone).projection
  factorization f := by
    apply ObjectProperty.hom_ext
    change biprod.inl ≫ jointInclusion f.hom.hom ≫ SplitFactorization.projection f.hom.hom = _
    rw [← Category.assoc, jointInclusion, biprod.inl_desc]
    exact inclusion_projection f.hom.hom
  weak f := N.le_weq _ ((complexSubcategoryFactorization P hcone).weak f)

/-- The second actual endpoint retracts the original projection, for the quasi-isomorphism fine
model. -/
theorem complexJointDataOfNested_secondEndpointSection :
    RowFactorization.SecondEndpointSection N (complexJointDataOfNested P hcone hshift N) := by
  intro f
  apply ObjectProperty.hom_ext
  change biprod.inr ≫ jointInclusion f.hom.hom ≫ SplitFactorization.projection f.hom.hom = 𝟙 _
  rw [← Category.assoc, jointInclusion, biprod.inr_desc]
  exact biprod.inr_snd

/-- The unchanged row cylinder for the genuine quasi-isomorphism fine model. -/
def complexRowFactorizationOfNested (n : SimplexCategory) :
    FunctorialFactorization (RowWeakEquivalences.coarseStructure N n) :=
  RowFactorization.factorization N (complexJointDataOfNested P hcone hshift N) n

/-- Its actual inclusion component remains the identity-cone first factor. -/
@[simp] theorem complexRowFactorizationOfNested_inclusion_component {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj (complexSubcategory P) n)) (p : Interval n) :
    (((complexRowFactorizationOfNested P hcone hshift N n).inclusion.app f).hom.app p).hom =
      SplitFactorization.inclusion (f.hom.hom.app p).hom := by
  change biprod.inl ≫ jointInclusion (f.hom.hom.app p).hom = _
  exact biprod.inl_desc _ _

/-- Its actual projection component remains the original identity-cone projection. -/
@[simp] theorem complexRowFactorizationOfNested_projection_component {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj (complexSubcategory P) n)) (p : Interval n) :
    (((complexRowFactorizationOfNested P hcone hshift N n).projection.app f).hom.app p).hom =
      SplitFactorization.projection (f.hom.hom.app p).hom := rfl

/-- The second endpoint component is literally the original target biproduct inclusion. -/
@[simp] theorem complexJointDataOfNested_inr_comp_joint_component {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj (complexSubcategory P) n)) (p : Interval n) :
    ((complexJointDataOfNested P hcone hshift N).inr.app (Arrow.mk (f.hom.hom.app p))).hom ≫
      ((complexJointDataOfNested P hcone hshift N).joint.obj (Arrow.mk (f.hom.hom.app
          p))).obj.hom.hom =
      (biprod.inr : (f.right.obj.obj p).obj ⟶ SplitFactorization.middle (f.hom.hom.app p).hom) := by
  change biprod.inr ≫ jointInclusion (f.hom.hom.app p).hom = _
  exact biprod.inr_desc _ _


end CategoryTheory.Waldhausen.Fibration

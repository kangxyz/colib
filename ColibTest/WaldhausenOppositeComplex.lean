/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Waldhausen.Fibration.Rows.OppositeComplexJointInclusion
import Colib.CategoryTheory.Waldhausen.Fibration.Rows.OppositeComplexJointMap

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen CochainComplex
noncomputable section
universe u v u' v'
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (P : ObjectProperty (CochainComplex C ℤ)) (Q : ObjectProperty (CochainComplex D ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex D ℤ)).IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts]
  (hP : ∀ K, P K → P (K⟦(-1 : ℤ)⟧))
  (hQ : ∀ K, Q K → Q (K⟦(-1 : ℤ)⟧))

example : IsCompatibleDual (complexSubcategory P) (oppositeComplexSubcategory P) :=
  oppositeComplexSubcategory_compatible P

example {K L : P.FullSubcategoryᵒᵖ} (f : K ⟶ L) :
    (oppositeComplexSubcategory P).weq f ↔ QuasiIso f.unop.hom := Iff.rfl

example (f : Arrow P.FullSubcategoryᵒᵖ) :
    (oppositeComplexJointData P hP).inl.app f ≫
        ((oppositeComplexJointData P hP).joint.obj f).obj.hom ≫
        (oppositeComplexJointData P hP).projection.app f = f.hom :=
  (oppositeComplexJointData P hP).factorization f

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (hF : ∀ K, P K → Q ((F.mapHomologicalComplex (.up ℤ)).obj K))

example : IsExact (oppositeComplexSubcategory P).cof (oppositeComplexSubcategory P).weq
    (oppositeComplexSubcategory Q).cof (oppositeComplexSubcategory Q).weq
    (complexSubcategoryMap F P Q hF).op := complexSubcategoryMap_op_exact F P Q hF

example (f : Arrow P.FullSubcategoryᵒᵖ) :
    (oppositeComplexJointData Q hQ).inl.app
        ((complexSubcategoryMap F P Q hF).op.mapArrow.obj f) ≫
      ((oppositeComplexJointDataMapIso F P Q hF hP hQ
        (complexSubcategoryMap_op_exact F P Q hF)).inv.app f).hom.left =
    (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).inl.app f) :=
  oppositeComplexJointDataMapIso_inv_inl _ _ _ _ _ _ _ f

example {f g : Arrow P.FullSubcategoryᵒᵖ} (α : f ⟶ g) :
    ((oppositeComplexJointData P hP).joint ⋙
      ExtensionCategory.postcompose _ _ (complexSubcategoryMap_op_exact F P Q hF)).map α ≫
        (oppositeComplexJointDataMapIso F P Q hF hP hQ
          (complexSubcategoryMap_op_exact F P Q hF)).hom.app g =
      (oppositeComplexJointDataMapIso F P Q hF hP hQ
        (complexSubcategoryMap_op_exact F P Q hF)).hom.app f ≫
      ((complexSubcategoryMap F P Q hF).op.mapArrow ⋙
        (oppositeComplexJointData Q hQ).joint).map α :=
  (oppositeComplexJointDataMapIso F P Q hF hP hQ
    (complexSubcategoryMap_op_exact F P Q hF)).hom.naturality α

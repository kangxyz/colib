/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Duality.ComplexSubcategory
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Exact additive functors on actual complex subcategories

The literal degreewise functor preserves the inherited exact sequences. Its
opposite is Waldhausen-exact, with admissible epimorphisms as cofibrations.
No joint-cylinder comparison is an assumption.

Implementation provenance: the lifted functor is the one in
`Quillen/Waldhausen/Fibration/Rows/OppositeComplexJointMap.lean:54-57` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
namespace CategoryTheory.Waldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
  (P : ObjectProperty (CochainComplex C ℤ)) (Q : ObjectProperty (CochainComplex D ℤ))
  (hF : ∀ K, P K → Q ((F.mapHomologicalComplex (.up ℤ)).obj K))

/-- The original additive complex functor on the actual full subcategories. -/
def complexSubcategoryMap : P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F.mapHomologicalComplex (.up ℤ)) (fun K => hF K.obj K.property)


instance complexSubcategoryMap_additive : (complexSubcategoryMap F P Q hF).Additive := by
  dsimp [complexSubcategoryMap]
  infer_instance

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex D ℤ)).IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The actual lifted additive functor preserves the original ambient short exact sequences. -/
def complexSubcategoryExactMap : ExactCategory.ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex C ℤ)) P)
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex D ℤ)) Q) where
  toFunctor := complexSubcategoryMap F P Q hF
  map_conflation S hS := by
    exact hS.map_of_exact (F.mapHomologicalComplex (.up ℤ))

/-- Exactness of the opposite actual lifted functor follows from exactness of the
ambient additive functor, rather than being an extra cocylinder hypothesis. -/
theorem complexSubcategoryMap_op_exact :
    IsExact (oppositeComplexSubcategory P).cof (oppositeComplexSubcategory P).weq
      (oppositeComplexSubcategory Q).cof (oppositeComplexSubcategory Q).weq
      (complexSubcategoryMap F P Q hF).op where
  zero h := (complexSubcategoryMap F P Q hF).op.map_isZero h
  cofibration f hf := (complexSubcategoryExactMap F P Q hF).map_deflation f.unop hf
  weak f hf := by
    have : QuasiIso f.unop.hom := hf
    exact inferInstanceAs (QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.unop.hom))
  pushout hf hs :=
    ((complexSubcategoryExactMap F P Q hF).map_isPullback hs.unop hf).op

end CategoryTheory.Waldhausen

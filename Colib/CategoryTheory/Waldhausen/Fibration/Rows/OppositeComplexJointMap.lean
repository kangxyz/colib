/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.ComplexFunctor
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.AdditiveMap
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.OppositeComplexJoint

/-!
# Actual opposite joint cocylinders across additive functors

The common ambient cylinder gives a natural isomorphism for the original
opposite full-subcategory joint data across independent abelian categories.
Its source and middle maps are the actual biproduct and identity-cone maps,
transported through the original degree-reversing opposite equivalence.
Compatibility of the actual equivalence counit follows from the original
functor action on equality maps. Both endpoints and the weak projection retain
exact equations, including the inverse orientations needed by weak-arrow joint
data. The exactness assumption is on the actual displayed subcategory functor;
no cocylinder compatibility is assumed.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Fibration/Rows/OppositeComplexJointMap.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual complexes, maps and independent universes are retained. -/

@[expose] public section

open CochainComplex


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
  (P : ObjectProperty (CochainComplex C ℤ)) (Q : ObjectProperty (CochainComplex D ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex D ℤ)).IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts]
  (hF : ∀ K, P K → Q ((F.mapHomologicalComplex (.up ℤ)).obj K))


omit [P.ContainsZero] [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts] [Q.ContainsZero]
  [(abelianExactStructure (CochainComplex D ℤ)).IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts] in
/-- The original degree-reversal counit commutes with the actual additive complex functor. -/
lemma oppositePropertyEquivalence_counit_inv_map (K : P.FullSubcategoryᵒᵖ) :
    (complexSubcategoryMap F P Q hF).op.map ((oppositePropertyEquivalence P).counitIso.inv.app K) =
      (oppositePropertyEquivalence Q).counitIso.inv.app ((complexSubcategoryMap F P Q hF).op.obj
        K) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext n : 1
  dsimp [complexSubcategoryMap, oppositePropertyEquivalence, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, ObjectProperty.opEquivalence,
    CategoryTheory.Equivalence.congrFullSubcategory]
  simp only [HomologicalComplex.XIsoOfEq, HomologicalComplex.opUnitIso,
    HomologicalComplex.opInverse, HomologicalComplex.opFunctor,
    HomologicalComplex.Hom.isoOfComponents, op_X, unopSymm_X, Iso.refl_hom,
    Iso.refl_inv, NatIso.ofComponents_hom_app, Functor.id_obj, Functor.comp_obj,
    Iso.op_hom, Quiver.Hom.unop_op, eqToIso.hom, eqToHom_unop,
    neg_neg, eq_self, eqToHom_naturality, Category.comp_id,
    Functor.mapHomologicalComplex_obj_X]
  exact eqToHom_map F _

omit [P.ContainsZero] [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts] [Q.ContainsZero]
  [(abelianExactStructure (CochainComplex D ℤ)).IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts] in
/-- The original degree-reversal counit commutes with the actual additive complex functor. -/
lemma oppositePropertyEquivalence_counit_hom_map (K : P.FullSubcategoryᵒᵖ) :
    (complexSubcategoryMap F P Q hF).op.map ((oppositePropertyEquivalence P).counitIso.hom.app K) =
      (oppositePropertyEquivalence Q).counitIso.hom.app ((complexSubcategoryMap F P Q hF).op.obj
        K) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext n : 1
  dsimp [complexSubcategoryMap, oppositePropertyEquivalence, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, ObjectProperty.opEquivalence,
    CategoryTheory.Equivalence.congrFullSubcategory]
  simp only [HomologicalComplex.XIsoOfEq, HomologicalComplex.opUnitIso,
    HomologicalComplex.opInverse, HomologicalComplex.opFunctor,
    HomologicalComplex.Hom.isoOfComponents, op_X, unopSymm_X, Iso.refl_hom,
    Iso.refl_inv, NatIso.ofComponents_inv_app, Functor.id_obj, Functor.comp_obj,
    Iso.op_inv, Quiver.Hom.unop_op, eqToIso.inv, eqToHom_unop,
    neg_neg, eq_self, eqToHom_naturality, Category.comp_id,
    Functor.mapHomologicalComplex_obj_X]
  exact eqToHom_map F _

variable (hP : ∀ K, P K → P (K⟦(-1 : ℤ)⟧)) (hQ : ∀ K, Q K → Q (K⟦(-1 : ℤ)⟧))

/-- Source comparison uses the actual biproduct comparison in the opposite abelian category. -/
def oppositeJointSourceMapIso (f : Arrow P.FullSubcategoryᵒᵖ) :
    (complexSubcategoryMap F P Q hF).op.obj
        (((oppositeComplexJointData P hP).joint.obj f).obj.left) ≅
      (((oppositeComplexJointData Q hQ).joint.obj
        ((complexSubcategoryMap F P Q hF).op.mapArrow.obj f)).obj.left) :=
  by
    refine Iso.op (Q.isoMk ?_)
    exact ((CochainComplex.opEquivalence D).inverse.mapIso
      ((F.op.mapHomologicalComplex (.up ℤ)).mapBiprod
        (((oppositePropertyEquivalence P).inverse.mapArrow.obj f).left.obj)
        (((oppositePropertyEquivalence P).inverse.mapArrow.obj f).right.obj))).unop

/-- Middle comparison uses the original additive identity-cone cylinder comparison. -/
def oppositeJointMiddleMapIso (f : Arrow P.FullSubcategoryᵒᵖ) :
    (complexSubcategoryMap F P Q hF).op.obj
        (((oppositeComplexJointData P hP).joint.obj f).obj.right) ≅
      (((oppositeComplexJointData Q hQ).joint.obj
        ((complexSubcategoryMap F P Q hF).op.mapArrow.obj f)).obj.right) :=
  by
    refine Iso.op (Q.isoMk ?_)
    exact ((CochainComplex.opEquivalence D).inverse.mapIso
      (SplitFactorization.middleMapIso F.op
        (((oppositePropertyEquivalence P).inverse.mapArrow.obj f).hom.hom))).unop

lemma oppositeJointMapIso_comm (f : Arrow P.FullSubcategoryᵒᵖ) :
    (oppositeJointSourceMapIso F P Q hF hP hQ f).hom ≫
        ((oppositeComplexJointData Q hQ).joint.obj
          ((complexSubcategoryMap F P Q hF).op.mapArrow.obj f)).obj.hom =
      (complexSubcategoryMap F P Q hF).op.map
          (((oppositeComplexJointData P hP).joint.obj f).obj.hom) ≫
        (oppositeJointMiddleMapIso F P Q hF hP hQ f).hom := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext n : 1
  exact congrArg (fun t => (t.f (-n)).unop)
    (SplitFactorization.middleMapIso_jointInclusion F.op
      (((oppositePropertyEquivalence P).inverse.mapArrow.obj f).hom.hom)).symm

lemma oppositeJointSourceMapIso_naturality {f g : Arrow P.FullSubcategoryᵒᵖ} (α : f ⟶ g) :
    (complexSubcategoryMap F P Q hF).op.map (((oppositeComplexJointData P hP).joint.map
      α).hom.left) ≫
        (oppositeJointSourceMapIso F P Q hF hP hQ g).hom =
      (oppositeJointSourceMapIso F P Q hF hP hQ f).hom ≫
        ((oppositeComplexJointData Q hQ).joint.map
          ((complexSubcategoryMap F P Q hF).op.mapArrow.map α)).hom.left := by
  let a := ((oppositePropertyEquivalence P).inverse.mapArrow.map α).left.hom
  let b := ((oppositePropertyEquivalence P).inverse.mapArrow.map α).right.hom
  have h : (F.op.mapHomologicalComplex (.up ℤ)).map (biprod.map a b) ≫
      ((F.op.mapHomologicalComplex (.up ℤ)).mapBiprod _ _).hom =
        ((F.op.mapHomologicalComplex (.up ℤ)).mapBiprod _ _).hom ≫
          biprod.map ((F.op.mapHomologicalComplex (.up ℤ)).map a)
            ((F.op.mapHomologicalComplex (.up ℤ)).map b) := by
    apply biprod.hom_ext <;> simp [← CategoryTheory.Functor.map_comp]
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext n : 1
  exact congrArg (fun t => (t.f (-n)).unop) h

lemma oppositeJointMiddleMapIso_naturality {f g : Arrow P.FullSubcategoryᵒᵖ} (α : f ⟶ g) :
    (complexSubcategoryMap F P Q hF).op.map (((oppositeComplexJointData P hP).joint.map
      α).hom.right) ≫
        (oppositeJointMiddleMapIso F P Q hF hP hQ g).hom =
      (oppositeJointMiddleMapIso F P Q hF hP hQ f).hom ≫
        ((oppositeComplexJointData Q hQ).joint.map
          ((complexSubcategoryMap F P Q hF).op.mapArrow.map α)).hom.right := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext n : 1
  exact congrArg (fun t => (t.f (-n)).unop)
    (SplitFactorization.middleMapIso_naturality F.op
      ((oppositeProperty P).ι.mapArrow.map ((oppositePropertyEquivalence P).inverse.mapArrow.map
        α)))

lemma oppositeJointSourceMapIso_inl (f : Arrow P.FullSubcategoryᵒᵖ) :
    (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).inl.app f) ≫
        (oppositeJointSourceMapIso F P Q hF hP hQ f).hom =
      (oppositeComplexJointData Q hQ).inl.app ((complexSubcategoryMap F P Q hF).op.mapArrow.obj
        f) := by
  dsimp only [oppositeComplexJointData,
    Fibration.RowFactorization.JointData.ofExactEquivalence,
    Fibration.RowFactorization.equivalenceInl]
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [oppositePropertyEquivalence_counit_inv_map F P Q hF]
  congr 1
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext n : 1
  have h : (F.op.mapHomologicalComplex (.up ℤ)).map
      (biprod.inl : ((oppositePropertyEquivalence P).inverse.mapArrow.obj f).left.obj ⟶
        ((oppositePropertyEquivalence P).inverse.mapArrow.obj f).left.obj ⊞
          ((oppositePropertyEquivalence P).inverse.mapArrow.obj f).right.obj) ≫
      ((F.op.mapHomologicalComplex (.up ℤ)).mapBiprod _ _).hom = biprod.inl := by
    apply biprod.hom_ext <;> simp [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun t => (t.f (-n)).unop) h

lemma oppositeJointSourceMapIso_inr (f : Arrow P.FullSubcategoryᵒᵖ) :
    (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).inr.app f) ≫
        (oppositeJointSourceMapIso F P Q hF hP hQ f).hom =
      (oppositeComplexJointData Q hQ).inr.app ((complexSubcategoryMap F P Q hF).op.mapArrow.obj
        f) := by
  dsimp only [oppositeComplexJointData,
    Fibration.RowFactorization.JointData.ofExactEquivalence,
    Fibration.RowFactorization.equivalenceInr]
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [oppositePropertyEquivalence_counit_inv_map F P Q hF]
  congr 1
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext n : 1
  have h : (F.op.mapHomologicalComplex (.up ℤ)).map
      (biprod.inr : ((oppositePropertyEquivalence P).inverse.mapArrow.obj f).right.obj ⟶
        ((oppositePropertyEquivalence P).inverse.mapArrow.obj f).left.obj ⊞
          ((oppositePropertyEquivalence P).inverse.mapArrow.obj f).right.obj) ≫
      ((F.op.mapHomologicalComplex (.up ℤ)).mapBiprod _ _).hom = biprod.inr := by
    apply biprod.hom_ext <;> simp [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun t => (t.f (-n)).unop) h

lemma oppositeJointMiddleMapIso_projection (f : Arrow P.FullSubcategoryᵒᵖ) :
    (oppositeJointMiddleMapIso F P Q hF hP hQ f).hom ≫
        (oppositeComplexJointData Q hQ).projection.app ((complexSubcategoryMap F P Q
          hF).op.mapArrow.obj f) =
      (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).projection.app f)
        := by
  dsimp only [oppositeComplexJointData,
    Fibration.RowFactorization.JointData.ofExactEquivalence,
    Fibration.RowFactorization.equivalenceProjection]
  rw [CategoryTheory.Functor.map_comp]
  erw [oppositePropertyEquivalence_counit_hom_map F P Q hF]
  rw [← Category.assoc]
  congr 1
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext n : 1
  exact congrArg (fun t => (t.f (-n)).unop)
    (SplitFactorization.middleMapIso_projection F.op
      (((oppositePropertyEquivalence P).inverse.mapArrow.obj f).hom.hom))

variable (hExact : IsExact (oppositeComplexSubcategory P).cof (oppositeComplexSubcategory P).weq
  (oppositeComplexSubcategory Q).cof (oppositeComplexSubcategory Q).weq
  (complexSubcategoryMap F P Q hF).op)

/-- The actual common cocylinder is compatible with this exact cross-category additive complex
functor. -/
def oppositeComplexJointDataMapIso :
    (oppositeComplexJointData P hP).joint ⋙
      ExtensionCategory.postcompose (oppositeComplexSubcategory P) (oppositeComplexSubcategory
        Q) hExact ≅
    (complexSubcategoryMap F P Q hF).op.mapArrow ⋙ (oppositeComplexJointData Q hQ).joint :=
  NatIso.ofComponents (fun f => (ExtensionCategory.objects (oppositeComplexSubcategory Q)).isoMk
    (Arrow.isoMk (oppositeJointSourceMapIso F P Q hF hP hQ f)
      (oppositeJointMiddleMapIso F P Q hF hP hQ f)
      (oppositeJointMapIso_comm F P Q hF hP hQ f))) (by
        intro f g α
        apply ObjectProperty.hom_ext
        apply Arrow.hom_ext
        · exact oppositeJointSourceMapIso_naturality F P Q hF hP hQ α
        · exact oppositeJointMiddleMapIso_naturality F P Q hF hP hQ α)

/-- The packaged natural comparison retains the first original endpoint. -/
lemma oppositeComplexJointDataMapIso_inl (f : Arrow P.FullSubcategoryᵒᵖ) :
    (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).inl.app f) ≫
        ((oppositeComplexJointDataMapIso F P Q hF hP hQ hExact).hom.app f).hom.left =
      (oppositeComplexJointData Q hQ).inl.app
        ((complexSubcategoryMap F P Q hF).op.mapArrow.obj f) :=
  oppositeJointSourceMapIso_inl F P Q hF hP hQ f

/-- The packaged natural comparison retains the second original endpoint. -/
lemma oppositeComplexJointDataMapIso_inr (f : Arrow P.FullSubcategoryᵒᵖ) :
    (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).inr.app f) ≫
        ((oppositeComplexJointDataMapIso F P Q hF hP hQ hExact).hom.app f).hom.left =
      (oppositeComplexJointData Q hQ).inr.app
        ((complexSubcategoryMap F P Q hF).op.mapArrow.obj f) :=
  oppositeJointSourceMapIso_inr F P Q hF hP hQ f

/-- The packaged natural comparison retains the original weak projection. -/
lemma oppositeComplexJointDataMapIso_projection (f : Arrow P.FullSubcategoryᵒᵖ) :
    ((oppositeComplexJointDataMapIso F P Q hF hP hQ hExact).hom.app f).hom.right ≫
        (oppositeComplexJointData Q hQ).projection.app
          ((complexSubcategoryMap F P Q hF).op.mapArrow.obj f) =
      (complexSubcategoryMap F P Q hF).op.map
        ((oppositeComplexJointData P hP).projection.app f) :=
  oppositeJointMiddleMapIso_projection F P Q hF hP hQ f

/-- The actual inverse comparison retains the first original endpoint. -/
lemma oppositeComplexJointDataMapIso_inv_inl (f : Arrow P.FullSubcategoryᵒᵖ) :
    (oppositeComplexJointData Q hQ).inl.app ((complexSubcategoryMap F P Q hF).op.mapArrow.obj f) ≫
        ((oppositeComplexJointDataMapIso F P Q hF hP hQ hExact).inv.app f).hom.left =
      (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).inl.app f) := by
  change _ ≫ (oppositeJointSourceMapIso F P Q hF hP hQ f).inv = _
  rw [← oppositeJointSourceMapIso_inl F P Q hF hP hQ f, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The actual inverse comparison retains the second original endpoint. -/
lemma oppositeComplexJointDataMapIso_inv_inr (f : Arrow P.FullSubcategoryᵒᵖ) :
    (oppositeComplexJointData Q hQ).inr.app ((complexSubcategoryMap F P Q hF).op.mapArrow.obj f) ≫
        ((oppositeComplexJointDataMapIso F P Q hF hP hQ hExact).inv.app f).hom.left =
      (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).inr.app f) := by
  change _ ≫ (oppositeJointSourceMapIso F P Q hF hP hQ f).inv = _
  rw [← oppositeJointSourceMapIso_inr F P Q hF hP hQ f, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The actual inverse comparison retains the original weak projection. -/
lemma oppositeComplexJointDataMapIso_inv_projection (f : Arrow P.FullSubcategoryᵒᵖ) :
    ((oppositeComplexJointDataMapIso F P Q hF hP hQ hExact).inv.app f).hom.right ≫
        (complexSubcategoryMap F P Q hF).op.map ((oppositeComplexJointData P hP).projection.app f) =
      (oppositeComplexJointData Q hQ).projection.app ((complexSubcategoryMap F P Q
        hF).op.mapArrow.obj f) := by
  change (oppositeJointMiddleMapIso F P Q hF hP hQ f).inv ≫ _ = _
  rw [← oppositeJointMiddleMapIso_projection F P Q hF hP hQ f, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0311",
  colib_ref "quillen" "Quillen/Waldhausen/Fibration/Rows/OppositeComplexJointMap.lean:60-291"
    "adaptation" "The actual additive biproduct and identity-cone comparison, its full naturality, \
    and both endpoint orientations"]
  CategoryTheory.Waldhausen.oppositeComplexJointDataMapIso
  CategoryTheory.Waldhausen.oppositeJointSourceMapIso_inl
  CategoryTheory.Waldhausen.oppositeJointSourceMapIso_inr
  CategoryTheory.Waldhausen.oppositeJointMiddleMapIso_projection
  CategoryTheory.Waldhausen.oppositeComplexJointDataMapIso_inv_inl
  CategoryTheory.Waldhausen.oppositeComplexJointDataMapIso_inv_inr
  CategoryTheory.Waldhausen.oppositeComplexJointDataMapIso_inv_projection

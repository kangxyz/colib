/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
Source: `Quillen/KTheory/Bass/TwoChart.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

The actual cokernel of two endofunctor chart maps on an arbitrary category, with independent object,
morphism and group universes. Includes the original representative map, exactness, kernel relations,
natural transformations and unique descent; no additivity hypothesis on the source functor is used.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace KTheory.Bass.TwoChart
variable {D : Type u} [Category.{w} D] {P L : D ⥤ D} (p m : P ⟶ L)

/-- The actual two polynomial charts map to the Laurent group by their difference. -/
def polynomialDifference (F : D ⥤ AddCommGrpCat.{v}) (R : D) :
    F.obj (P.obj R) ⊞ F.obj (P.obj R) ⟶
      F.obj (L.obj R) :=
  biprod.desc (F.map (p.app R)) (-F.map (m.app R))

@[reassoc] lemma polynomialDifference_naturality (F : D ⥤ AddCommGrpCat.{v})
    {R S : D} (f : R ⟶ S) :
    biprod.map (F.map (P.map f)) (F.map (P.map f)) ≫
      polynomialDifference p m F S = polynomialDifference p m F R ≫ F.map (L.map f) := by
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc,polynomialDifference,biprod.inl_desc_assoc,
      biprod.inl_desc,← F.map_comp]
    rw [p.naturality]
  · simp only [biprod.inr_map_assoc,polynomialDifference,biprod.inr_desc_assoc,
      biprod.inr_desc,Preadditive.comp_neg,Preadditive.neg_comp,← F.map_comp]
    rw [m.naturality]

/-- Ring maps give literal commuting squares of polynomial-difference homomorphisms. -/
def polynomialDifferenceDiagram (F : D ⥤ AddCommGrpCat.{v}) :
    D ⥤ Arrow AddCommGrpCat.{v} where
  obj R := Arrow.mk (polynomialDifference p m F R)
  map f := Arrow.homMk
    (biprod.map (F.map (P.map f)) (F.map (P.map f)))
    (F.map (L.map f)) (polynomialDifference_naturality p m F f)
  map_id R := by
    apply Arrow.hom_ext
    · apply biprod.hom_ext <;> simp
    · simp
  map_comp f g := by
    apply Arrow.hom_ext
    · apply biprod.hom_ext <;> simp
    · simp

/-- Bass contraction is the genuine categorical cokernel of the two chart maps. -/
def contraction (F : D ⥤ AddCommGrpCat.{v}) :
    D ⥤ AddCommGrpCat.{v} := polynomialDifferenceDiagram p m F ⋙ coker AddCommGrpCat

/-- The original Laurent-to-cokernel projection, natural in the coefficient ring. -/
def contractionπ (F : D ⥤ AddCommGrpCat.{v}) :
    L ⋙ F ⟶ contraction p m F where
  app R := cokernel.π (polynomialDifference p m F R)
  naturality {R S} f := by
    simp [contraction, polynomialDifferenceDiagram, coker]

@[reassoc (attr := simp)] lemma polynomialDifference_contractionπ
    (F : D ⥤ AddCommGrpCat.{v}) (R : D) :
    polynomialDifference p m F R ≫ (contractionπ p m F).app R = 0 := cokernel.condition _

/-- Descent from the actual Laurent group through the Bass quotient. -/
def contractionDesc (F : D ⥤ AddCommGrpCat.{v}) (R : D)
    {A : AddCommGrpCat.{v}} (f : F.obj (L.obj R) ⟶ A)
    (hf : polynomialDifference p m F R ≫ f = 0) : (contraction p m F).obj R ⟶ A :=
  cokernel.desc _ f hf

@[reassoc (attr := simp)] lemma contractionπ_desc
    (F : D ⥤ AddCommGrpCat.{v}) (R : D)
    {A : AddCommGrpCat.{v}} (f : F.obj (L.obj R) ⟶ A)
    (hf : polynomialDifference p m F R ≫ f = 0) :
    (contractionπ p m F).app R ≫ contractionDesc p m F R f hf = f := cokernel.π_desc _ _ _

lemma contraction_hom_ext (F : D ⥤ AddCommGrpCat.{v}) (R : D)
    {A : AddCommGrpCat.{v}} {f g : (contraction p m F).obj R ⟶ A}
    (h : (contractionπ p m F).app R ≫ f = (contractionπ p m F).app R ≫ g) : f = g :=
  (cancel_epi (cokernel.π (polynomialDifference p m F R))).mp h

/-- The actual presentation is right exact, without any hypothesis on F. -/
lemma contraction_exact (F : D ⥤ AddCommGrpCat.{v}) (R : D) :
    (ShortComplex.mk (polynomialDifference p m F R) ((contractionπ p m F).app R)
      (polynomialDifference_contractionπ p m F R)).Exact :=
  ShortComplex.cokernelSequence_exact (polynomialDifference p m F R)

instance contractionπ_epi (F : D ⥤ AddCommGrpCat.{v}) (R : D) :
    Epi ((contractionπ p m F).app R) := by
  change Epi (cokernel.π (polynomialDifference p m F R))
  infer_instance

@[reassoc (attr := simp)] lemma plus_contractionπ
    (F : D ⥤ AddCommGrpCat.{v}) (R : D) :
    F.map (p.app R) ≫ (contractionπ p m F).app R = 0 := by
  simpa [polynomialDifference] using congrArg (fun f ↦ biprod.inl ≫ f)
    (polynomialDifference_contractionπ p m F R)

@[reassoc (attr := simp)] lemma minus_contractionπ
    (F : D ⥤ AddCommGrpCat.{v}) (R : D) :
    F.map (m.app R) ≫ (contractionπ p m F).app R = 0 := by
  simpa [polynomialDifference] using congrArg (fun f ↦ biprod.inr ≫ f)
    (polynomialDifference_contractionπ p m F R)

/-- The categorical cokernel is the ordinary quotient by the original difference image. -/
def contractionQuotientIso (F : D ⥤ AddCommGrpCat.{v}) (R : D) :
    (contraction p m F).obj R ≅ AddCommGrpCat.of
      (F.obj (L.obj R) ⧸ AddMonoidHom.range (polynomialDifference p m F R).hom) :=
  AddCommGrpCat.cokernelIsoQuotient (polynomialDifference p m F R)

@[reassoc (attr := simp)] lemma contractionπ_quotientIso
    (F : D ⥤ AddCommGrpCat.{v}) (R : D) :
    (contractionπ p m F).app R ≫ (contractionQuotientIso p m F R).hom =
      AddCommGrpCat.ofHom (QuotientAddGroup.mk' _) := by
  exact cokernel.π_desc _ _ _

/-- Natural transformations of original group functors induce the original difference square. -/
def polynomialDifferenceTransformation {F G : D ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) : polynomialDifferenceDiagram p m F ⟶ polynomialDifferenceDiagram p m G where
  app R := Arrow.homMk (biprod.map (α.app _) (α.app _)) (α.app _) (by
    apply biprod.hom_ext' <;> simp [polynomialDifferenceDiagram, polynomialDifference,
      α.naturality])
  naturality {R S} f := by
    apply Arrow.hom_ext
    · apply biprod.hom_ext <;> simp [polynomialDifferenceDiagram, α.naturality]
    · exact α.naturality _

/-- The genuine induced map of Bass cokernels, natural in every coefficient ring. -/
def contractionMap {F G : D ⥤ AddCommGrpCat.{v}} (α : F ⟶ G) :
    contraction p m F ⟶ contraction p m G :=
  Functor.whiskerRight (polynomialDifferenceTransformation p m α) (coker AddCommGrpCat)

@[reassoc (attr := simp)] lemma contractionMap_π
    {F G : D ⥤ AddCommGrpCat.{v}} (α : F ⟶ G) (R : D) :
    (contractionπ p m F).app R ≫ (contractionMap p m α).app R =
      α.app (L.obj R) ≫ (contractionπ p m G).app R := by
  simp [contractionMap, polynomialDifferenceTransformation, polynomialDifferenceDiagram,
    contractionπ, coker]

@[simp] lemma contractionMap_id (F : D ⥤ AddCommGrpCat.{v}) :
    contractionMap p m (𝟙 F) = 𝟙 (contraction p m F) := by
  apply NatTrans.ext
  funext R
  apply contraction_hom_ext p m F R
  simp

@[simp] lemma contractionMap_comp {F G H : D ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) (β : G ⟶ H) :
    contractionMap p m (α ≫ β) = contractionMap p m α ≫ contractionMap p m β := by
  apply NatTrans.ext
  funext R
  apply contraction_hom_ext p m F R
  simp

/-- Bass contraction is an actual endofunctor on ring-indexed abelian group functors. -/
def contractionFunctor :
    (D ⥤ AddCommGrpCat.{v}) ⥤ (D ⥤ AddCommGrpCat.{v}) where
  obj := contraction p m
  map := contractionMap p m
  map_id := contractionMap_id p m
  map_comp := contractionMap_comp p m

end KTheory.Bass.TwoChart

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace KTheory.Bass.TwoChart
variable {D : Type u} [Category.{w} D] {P L : D ⥤ D} (p m : P ⟶ L)

/-- The actual presentation homomorphism is literally plus(a) minus minus(b). -/
lemma polynomialDifference_pair (F : D ⥤ AddCommGrpCat.{v}) (R : D)
    (a b : F.obj (P.obj R)) :
    polynomialDifference p m F R ((AddCommGrpCat.biprodIsoProd _ _).inv (a,b)) =
      F.map (p.app R) a - F.map (m.app R) b := by
  have h := AddCommGrpCat.biprodIsoProd_inv_comp_desc (F.map (p.app R)) (-F.map (m.app R))
  simpa [polynomialDifference, sub_eq_add_neg] using congrArg (fun f ↦ f (a,b)) h

/-- Every Bass class has an original Laurent representative. -/
lemma contractionπ_surjective (F : D ⥤ AddCommGrpCat.{v}) (R : D) :
    Function.Surjective ((contractionπ p m F).app R) :=
  (AddCommGrpCat.epi_iff_surjective _).mp inferInstance

/-- A Laurent class vanishes precisely when it is an actual difference of the two chart images. -/
lemma contractionπ_eq_zero_iff (F : D ⥤ AddCommGrpCat.{v}) (R : D)
    (x : F.obj (L.obj R)) :
    (contractionπ p m F).app R x = 0 ↔ ∃ a b : F.obj (P.obj R),
      F.map (p.app R) a - F.map (m.app R) b = x := by
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := (ShortComplex.ab_exact_iff _).mp (contraction_exact p m F R) x hx
    let e := AddCommGrpCat.biprodIsoProd (F.obj (P.obj R)) (F.obj (P.obj R))
    refine ⟨(e.hom y).1,(e.hom y).2,?_⟩
    rw [← polynomialDifference_pair p m]
    simpa [e] using hy
  · rintro ⟨a,b,rfl⟩
    rw [← polynomialDifference_pair p m]
    exact congrArg (fun f ↦ f ((AddCommGrpCat.biprodIsoProd _ _).inv (a,b)))
      (polynomialDifference_contractionπ p m F R)

/-- A map killing both original chart images descends uniquely through the actual Bass cokernel. -/
def contractionDescOfCharts (F : D ⥤ AddCommGrpCat.{v}) (R : D)
    {A : AddCommGrpCat.{v}} (f : F.obj (L.obj R) ⟶ A)
    (hp : F.map (p.app R) ≫ f = 0) (hm : F.map (m.app R) ≫ f = 0) :
    (contraction p m F).obj R ⟶ A :=
  contractionDesc p m F R f (by apply biprod.hom_ext' <;> simp [polynomialDifference,hp,hm])

@[reassoc (attr := simp)] lemma contractionπ_descOfCharts
    (F : D ⥤ AddCommGrpCat.{v}) (R : D)
    {A : AddCommGrpCat.{v}} (f : F.obj (L.obj R) ⟶ A)
    (hp : F.map (p.app R) ≫ f = 0) (hm : F.map (m.app R) ≫ f = 0) :
    (contractionπ p m F).app R ≫ contractionDescOfCharts p m F R f hp hm = f :=
  contractionπ_desc p m F R f _

/-- If the plus chart is already surjective, its Bass cokernel is genuinely zero. -/
lemma contraction_isZero_of_epi_plus (F : D ⥤ AddCommGrpCat.{v}) (R : D)
    [Epi (F.map (p.app R))] : IsZero ((contraction p m F).obj R) := by
  apply IsZero.of_epi_eq_zero ((contractionπ p m F).app R)
  exact (cancel_epi (F.map (p.app R))).mp (by simp)

/-- In particular the construction kills actual constant group functors. -/
lemma contraction_constant_isZero (A : AddCommGrpCat.{v}) (R : D) :
    IsZero ((contraction p m ((Functor.const D).obj A)).obj R) := by
  let : Epi (((Functor.const D).obj A).map (p.app R)) := by
    change Epi (𝟙 A)
    infer_instance
  exact contraction_isZero_of_epi_plus p m _ _

end KTheory.Bass.TwoChart

end

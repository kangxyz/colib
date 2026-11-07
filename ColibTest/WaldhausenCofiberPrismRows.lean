/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.CofiberPrismFaces
public import Colib.CategoryTheory.Waldhausen.SConstruction.ObjectTransformationSquare
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakObjectCompositionPrism

/-!
# Source-only regressions for the actual cofiber-prism rows

The five extracted definitions are checked against their complete original expressions.
The remaining assertions retain entire row/grid functors, original components, all five
faces, mixed maps, independent simplex operators and strict chosen-zero hypotheses.
The row-transformation component retains four universes. No assertion below has been
compiled in this source-only preparation, and no topological realization is imported.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial

universe u v u' v'

namespace ColibTest.WaldhausenCofiberPrismRows

section ExtractedDefinitions

variable {C : Type u} [Category.{v} C] (W : Structure C)

example (n : SimplexCategory) :
    Structure.intervalProjection n =
      (show Monotone (fun p : Grid n ↦ p.2) from fun _ _ h ↦ h.2).functor := rfl

example {n : SimplexCategory} (F : QuotientRows.Obj W n) :
    W.rowSimplex F =
      ⟨Structure.intervalProjection n ⋙ F.obj, {
        zero _ i := F.property.zero i
        cofibration _ i j k hij hjk := F.property.cofibration i j k hij hjk
        quotient _ i j k hij hjk := F.property.quotient i j k hij hjk
        weak s t i j hst hij := by
          change W.weq (F.obj.map (𝟙 (interval i j hij)))
          rw [F.obj.map_id]
          exact W.weq.id_mem (F.obj.obj (interval i j hij)) }⟩ := rfl

example (A : C) :
    W.kZeroObjectSimplex A = W.rowSimplex ((oneEmbedding W).obj A) := rfl

example {A B : C} (f : A ⟶ B) (hf : W.weq f) :
    W.oneWeakArrow f hf =
      ⟨(oneEmbedding W).map f, (oneEmbedding_exact W).weak f hf⟩ := rfl

example {A B : C} (f : A ⟶ B) (hf : W.weq f) :
    W.weakObjectSimplex f hf =
      ⟨weakChainToGrid W (ComposableArrows.mk₁ (W.oneWeakArrow f hf)),
        (isSimplex₂_diagonal_iff W.cof W.weq _).mp
          (weakChainToGrid_isSimplex₂ W _)⟩ := rfl

example {n : SimplexCategory} (F : QuotientRows.Obj W n) (t) (p : Interval n) :
    (W.rowSimplex F).val.obj (t, p) = F.obj.obj p := rfl

example {n : SimplexCategory} (F : QuotientRows.Obj W n) {p r : Grid n} (a : p ⟶ r) :
    (W.rowSimplex F).val.map a = F.obj.map (homOfLE (leOfHom a).2) := rfl

example (A : C) (t : Fin 2) :
    (W.kZeroObjectSimplex A).val.obj (grid t 0 1 (by decide)) = A := rfl

example {A B : C} (f : A ⟶ B) (hf : W.weq f) :
    (W.oneWeakArrow f hf).hom.hom.app (interval 0 1 (by decide)) = f := rfl

example {A B : C} (f : A ⟶ B) (hf : W.weq f) :
    (W.weakObjectSimplex f hf).val.obj (grid 0 0 1 (by decide)) = A := rfl

example {A B : C} (f : A ⟶ B) (hf : W.weq f) :
    (W.weakObjectSimplex f hf).val.obj (grid 1 0 1 (by decide)) = B := rfl

example {A B : C} (f : A ⟶ B) (hf : W.weq f) {p r : Grid ⦋1⦌} (a : p ⟶ r) :
    (W.weakObjectSimplex f hf).val.map a =
      ((ComposableArrows.mk₁ (W.oneWeakArrow f hf)).obj p.1).obj.obj.map
          (homOfLE (leOfHom a).2) ≫
        ((ComposableArrows.mk₁ (W.oneWeakArrow f hf)).map
          (homOfLE (leOfHom a).1)).hom.hom.app r.2 := rfl

end ExtractedDefinitions

section Cofiber

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

include hi hwi hQ in
example : W.weq (0 : W.zero ⟶ Q) := cofiberTwo_quotient_weak W i q hi hwi hQ

example (p : Interval ⦋2⦌) (h02 : p ≠ interval 0 2 (by decide))
    (h12 : p ≠ interval 1 2 (by decide)) :
    cofiberTwoObject W (A := A) (B := A) (Q := W.zero) p =
      cofiberTwoObject W (A := A) (B := B) (Q := Q) p :=
  cofiberTwoComparison_object_eq W p h02 h12

example : cofiberTwoComparisonComponent W (Q := Q) i (interval 0 1 (by decide)) =
    𝟙 A := by
  simp [cofiberTwoComparisonComponent, cofiberTwoComparison_object_eq, interval]

example : cofiberTwoComparisonComponent W (Q := Q) i (interval 0 2 (by decide)) =
    i := by
  simp [cofiberTwoComparisonComponent, interval]

example : cofiberTwoComparisonComponent W (Q := Q) i (interval 1 2 (by decide)) =
    (0 : W.zero ⟶ Q) := by
  simp [cofiberTwoComparisonComponent, interval]

example {p r : Interval ⦋2⦌} (a : p ⟶ r) :
    (cofiberTwoDiagram W (𝟙 A) (0 : A ⟶ W.zero) (by simp)).map a ≫
        (cofiberTwoComparison W i q (cofiberTwo_comp_eq_zero W i q hQ)).app r =
      (cofiberTwoComparison W i q (cofiberTwo_comp_eq_zero W i q hQ)).app p ≫
        (cofiberTwoDiagram W i q (cofiberTwo_comp_eq_zero W i q hQ)).map a :=
  (cofiberTwoComparison W i q (cofiberTwo_comp_eq_zero W i q hQ)).naturality a

example : (cofiberTwoRowComparison W i q hi hQ).hom =
    cofiberTwoComparison W i q (cofiberTwo_comp_eq_zero W i q hQ) := rfl

include hwi in
example : weq W ⦋2⦌ (cofiberTwoRowComparison W i q hi hQ) :=
  cofiberTwoRowComparison_weak W i q hi hwi hQ

example : (cofiberTwoWeakArrow W i q hi hwi hQ).hom =
    cofiberTwoRowComparison W i q hi hQ := rfl

example : cofiberTwoPrism W i q hi hwi hQ =
    weakChainToGrid W (ComposableArrows.mk₁ (cofiberTwoWeakArrow W i q hi hwi hQ)) := rfl

example : IsSimplex₂ W.cof W.weq (cofiberTwoPrism W i q hi hwi hQ) :=
  cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ

example : (cofiberTwoPrism W i q hi hwi hQ).obj (grid₂ 0 0 1 (by decide)) = A := rfl

example : (cofiberTwoPrism W i q hi hwi hQ).obj (grid₂ 1 0 1 (by decide)) = A := rfl

example : (cofiberTwoPrism W i q hi hwi hQ).obj (grid₂ 0 0 2 (by decide)) = A := rfl

example : (cofiberTwoPrism W i q hi hwi hQ).obj (grid₂ 1 0 2 (by decide)) = B := rfl

example : (cofiberTwoPrism W i q hi hwi hQ).obj (grid₂ 0 1 2 (by decide)) = W.zero := rfl

example : (cofiberTwoPrism W i q hi hwi hQ).obj (grid₂ 1 1 2 (by decide)) = Q := rfl

example (t : Fin 2) (a : Fin 3) :
    (cofiberTwoPrism W i q hi hwi hQ).obj (grid₂ t a a le_rfl) = W.zero := by
  fin_cases t <;> fin_cases a <;> rfl

example {p r : Grid₂ ⦋2⦌ ⦋1⦌} (a : p ⟶ r) :
    (cofiberTwoPrism W i q hi hwi hQ).map a =
      ((ComposableArrows.mk₁ (cofiberTwoWeakArrow W i q hi hwi hQ)).obj p.1).obj.obj.map
          (homOfLE (leOfHom a).2) ≫
        ((ComposableArrows.mk₁ (cofiberTwoWeakArrow W i q hi hwi hQ)).map
          (homOfLE (leOfHom a).1)).hom.hom.app r.2 := rfl

example : gridRestriction 0 ⋙ cofiberTwoPrism W i q hi hwi hQ =
    cofiberTwoDiagram W (𝟙 A) (0 : A ⟶ W.zero) (by simp) :=
  cofiberTwoPrism_zero W i q hi hwi hQ

example : gridRestriction 1 ⋙ cofiberTwoPrism W i q hi hwi hQ =
    cofiberTwoDiagram W i q (cofiberTwo_comp_eq_zero W i q hQ) :=
  cofiberTwoPrism_one W i q hi hwi hQ

example : gridMap₂ (SimplexCategory.δ (2 : Fin 3)) (𝟙 ⦋1⦌) ⋙
    cofiberTwoPrism W i q hi hwi hQ = (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val :=
  W.cofiberTwoPrism_source_face i q hi hwi hQ

example : gridMap₂ (SimplexCategory.δ (1 : Fin 3)) (𝟙 ⦋1⦌) ⋙
    cofiberTwoPrism W i q hi hwi hQ = (W.weakObjectSimplex i hwi).val :=
  W.cofiberTwoPrism_middle_face i q hi hwi hQ

example : gridMap₂ (SimplexCategory.δ (0 : Fin 3)) (𝟙 ⦋1⦌) ⋙
    cofiberTwoPrism W i q hi hwi hQ =
      (W.weakObjectSimplex (0 : W.zero ⟶ Q)
        (cofiberTwo_quotient_weak W i q hi hwi hQ)).val :=
  W.cofiberTwoPrism_quotient_face i q hi hwi hQ

-- The transports in these identities retain every mixed map, not just grid objects.
example {p r : Grid₂ ⦋1⦌ ⦋1⦌} (a : p ⟶ r) :
    (gridMap₂ (SimplexCategory.δ (2 : Fin 3)) (𝟙 ⦋1⦌) ⋙
        cofiberTwoPrism W i q hi hwi hQ).map a ≫
        (eqToHom (W.cofiberTwoPrism_source_face i q hi hwi hQ)).app r =
      (eqToHom (W.cofiberTwoPrism_source_face i q hi hwi hQ)).app p ≫
        (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val.map a :=
  (eqToHom (W.cofiberTwoPrism_source_face i q hi hwi hQ)).naturality a

example {p r : Grid₂ ⦋1⦌ ⦋1⦌} (a : p ⟶ r) :
    (gridMap₂ (SimplexCategory.δ (1 : Fin 3)) (𝟙 ⦋1⦌) ⋙
        cofiberTwoPrism W i q hi hwi hQ).map a ≫
        (eqToHom (W.cofiberTwoPrism_middle_face i q hi hwi hQ)).app r =
      (eqToHom (W.cofiberTwoPrism_middle_face i q hi hwi hQ)).app p ≫
        (W.weakObjectSimplex i hwi).val.map a :=
  (eqToHom (W.cofiberTwoPrism_middle_face i q hi hwi hQ)).naturality a

example {p r : Grid₂ ⦋1⦌ ⦋1⦌} (a : p ⟶ r) :
    (gridMap₂ (SimplexCategory.δ (0 : Fin 3)) (𝟙 ⦋1⦌) ⋙
        cofiberTwoPrism W i q hi hwi hQ).map a ≫
        (eqToHom (W.cofiberTwoPrism_quotient_face i q hi hwi hQ)).app r =
      (eqToHom (W.cofiberTwoPrism_quotient_face i q hi hwi hQ)).app p ≫
        (W.weakObjectSimplex (0 : W.zero ⟶ Q)
          (cofiberTwo_quotient_weak W i q hi hwi hQ)).val.map a :=
  (eqToHom (W.cofiberTwoPrism_quotient_face i q hi hwi hQ)).naturality a

example {p r : Interval ⦋2⦌} (a : p ⟶ r) :
    (gridRestriction 0 ⋙ cofiberTwoPrism W i q hi hwi hQ).map a ≫
        (eqToHom (cofiberTwoPrism_zero W i q hi hwi hQ)).app r =
      (eqToHom (cofiberTwoPrism_zero W i q hi hwi hQ)).app p ≫
        (cofiberTwoDiagram W (𝟙 A) (0 : A ⟶ W.zero) (by simp)).map a :=
  (eqToHom (cofiberTwoPrism_zero W i q hi hwi hQ)).naturality a

example {p r : Interval ⦋2⦌} (a : p ⟶ r) :
    (gridRestriction 1 ⋙ cofiberTwoPrism W i q hi hwi hQ).map a ≫
        (eqToHom (cofiberTwoPrism_one W i q hi hwi hQ)).app r =
      (eqToHom (cofiberTwoPrism_one W i q hi hwi hQ)).app p ≫
        (cofiberTwoDiagram W i q (cofiberTwo_comp_eq_zero W i q hQ)).map a :=
  (eqToHom (cofiberTwoPrism_one W i q hi hwi hQ)).naturality a

end Cofiber

section IndependentSimplices

variable {C : Type u} [Category.{v} C] (W : Structure C)

example {n k l : SimplexCategory}
    (F : ComposableArrows (WeakRows W n) k.len) (α : l ⟶ k) :
    gridMap₂ (𝟙 n) α ⋙ weakChainToGrid W F =
      weakChainToGrid W (α.toOrderHom.monotone.functor ⋙ F) :=
  weakChainToGrid_precomp_nerve W F α

example {n m n' m' : SimplexCategory} (α : n' ⟶ n) (β : m' ⟶ m) :
    gridMap₂ α (𝟙 m') ⋙ gridMap₂ (𝟙 n) β =
      gridMap₂ (𝟙 n') β ⋙ gridMap₂ α (𝟙 m) := rfl

example {n m : ℕ} (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hF : IsSimplex₂ W.cof W.weq F)
    {n' m' : ℕ} (α : ⦋n'⦌ ⟶ ⦋n⦌) (β : ⦋m'⦌ ⟶ ⦋m⦌) :
    (SSet.stdSimplex.map α ⊗ₘ SSet.stdSimplex.map β) ≫ bisimplexFamily W F hF =
      bisimplexFamily W (gridMap₂ α β ⋙ F) (hF.precomp W.cof W.weq α β) :=
  bisimplexFamily_precomp W F hF α β

example {n m : ℕ} (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hF : IsSimplex₂ W.cof W.weq F)
    (k : SimplexCategoryᵒᵖ) (z : (Δ[n] ⊗ Δ[m] : SSet.{max u v}).obj k) :
    ((bisimplexFamily W F hF).app k z).val = gridMap₂ z.1.down z.2.down ⋙ F := rfl

example {n m : ℕ} (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hF : IsSimplex₂ W.cof W.weq F)
    (k : SimplexCategoryᵒᵖ) (z : (Δ[n] ⊗ Δ[m] : SSet.{max u v}).obj k)
    {p r : Grid k.unop} (a : p ⟶ r) :
    ((bisimplexFamily W F hF).app k z).val.map a =
      F.map ((gridMap₂ z.1.down z.2.down).map a) := rfl

example {A B : C} (f : A ⟶ B) (hf : W.weq f) {n : SimplexCategory}
    (α τ : n ⟶ ⦋1⦌) :
    nerveCylinderDiagram
        (whiskerLeft (Structure.intervalProjection n ⋙ indexMap α)
          ((oneEmbedding W).map f).hom) τ =
      gridMap₂ α τ ⋙ (W.weakObjectSimplex f hf).val :=
  W.weakObjectSimplex_cylinder f hf α τ

example {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g) :
    W.weakObjectCompositionPrism f g hf hg =
      weakChainToGrid W (ComposableArrows.mk₂ (W.oneWeakArrow f hf) (W.oneWeakArrow g hg)) := rfl

example {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g) :
    IsSimplex₂ W.cof W.weq (W.weakObjectCompositionPrism f g hf hg) :=
  W.weakObjectCompositionPrism_isSimplex₂ f g hf hg

example {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g) :
    gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.δ 2) ⋙ W.weakObjectCompositionPrism f g hf hg =
      (W.weakObjectSimplex f hf).val :=
  W.weakObjectCompositionPrism_first f g hf hg

example {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)
    (e : Fin 2) :
    (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ e) ⊗ₘ 𝟙 Δ[2]) ≫
        bisimplexFamily W (W.weakObjectCompositionPrism f g hf hg)
          (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) =
      SSet.const (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) :=
  W.weakObjectCompositionFamily_vertex f g hf hg e

end IndependentSimplices

section FourUniverses

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F) (η : F ⟶ G)
  (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)

include hF hF0 hG0 in
example (A : C) (p : Interval ⦋1⦌) :
    HEq (η.app ((oneDiagram V A).obj p))
      (((oneEmbedding W).map (η.app A)).hom.app p) :=
  oneDiagram_transformation_app V W hF η hF0 hG0 A p

include hF hF0 hG0 in
example (A : C) : HEq (η.app V.zero)
    (((oneEmbedding W).map (η.app A)).hom.app (interval 0 0 (by decide))) :=
  oneDiagram_transformation_app V W hF η hF0 hG0 A (interval 0 0 (by decide))

example (A : C) : HEq (η.app A)
    (((oneEmbedding W).map (η.app A)).hom.app (interval 0 1 (by decide))) := rfl

include hF hF0 hG0 in
example (A : C) : HEq (η.app V.zero)
    (((oneEmbedding W).map (η.app A)).hom.app (interval 1 1 (by decide))) :=
  oneDiagram_transformation_app V W hF η hF0 hG0 A (interval 1 1 (by decide))

end FourUniverses

section StrictTransformationCylinder

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))
  (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)

include hF0 hG0 in
example (A : C) :
    SSet.yonedaEquiv.symm (V.kZeroObjectSimplex A) ▷ Δ[1] ≫
        weakNaturalTransformationCylinder V W hF hG η hη =
      bisimplexFamily W (W.weakObjectSimplex (η.app A) (hη A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (η.app A) (hη A)).property) :=
  objectTransformationCylinder_square V W hF hG η hη hF0 hG0 A

end StrictTransformationCylinder

end ColibTest.WaldhausenCofiberPrismRows

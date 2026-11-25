/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectProjectionBinaryRows
public import Colib.KTheory.Waldhausen.Iterated.ReferenceWhiskeringFamily

/-!
# The outer and initial binary rows of the actual rectangle

The original rectangle nodes use the same normalized pullbacks and geometric comparisons
after precomposition. The outer row also uses the exact equality of total source functors.

Adapted from `RectangleOuterBinaryRow.lean` and `RectangleInitialBinaryRow.lean`
in `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS (asSmallCategory)
open CategoryTheory.Waldhausen.IteratedS.ModelSimplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectRectangleInitialBinaryRow

open BoundedFlatPerfectProjectionBinaryRows
open BoundedFlatPerfectDoubleSquareCommonSimplex
  (lastRightFunctorEq lastRightRawReference lastRightNormalizedReference)
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

private theorem preSource_transport {V₀ W₀ T₀ :
    WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (F : V₀ ⟶ T₀) (P : V₀ ⟶ W₀)
    {H H' : W₀ ⟶ T₀} (e : H.hom.toFunctor = H'.hom.toFunctor)
    (ρ : F.hom.toFunctor ≅ (P ≫ H).hom.toFunctor) :
    preReferenceNode F P ρ ⟨H, Iso.refl _⟩ =
      preReferenceNode F P (ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (eqToIso e))
        ⟨H', Iso.refl _⟩ := by
  have hh : H = H' := by
    apply WideSubcategory.hom_ext
    exact SmallWaldhausenCategory.Hom.ext e
  subst H'
  simp only [eqToIso_refl, isoWhiskerLeft_refl]
  have hρ : ρ ≪≫ Iso.refl (P.hom.toFunctor ⋙ H.hom.toFunctor) = ρ := Iso.trans_refl ρ
  exact congrArg (fun σ ↦ preReferenceNode F P (H := H) σ ⟨H, Iso.refl _⟩) hρ.symm

variable {V A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (F : asSmallCategory (W V) ⟶ asSmallCategory (W C'))
  (P : asSmallCategory (W V) ⟶ asSmallCategory (W A))
  (ρ : F.hom.toFunctor ≅ (P ≫ BoundedFlatPerfectTripleSimplex.source c q p).hom.toFunctor)

/-- The actual merged rectangle nodes, precomposed before changing the reference. -/
def preRectangleNodes (i : Fin 18) :=
  preReferenceNode F P ρ (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes
    p q p' q' a b c hp hq i)

/-- The initial three normalization labels on the rectangle. -/
def initialIndex : Fin 3 → Fin 18 := ![0, 1, 2]

/-- The outer three normalization labels on the rectangle. -/
def outerIndex : Fin 3 → Fin 18 := ![0, 14, 15]

/-- The initial binary source is the same actual total as the triple source. -/
def rectangleInitialReference :
    F.hom.toFunctor ≅ (P ≫ BoundedFlatPerfectBinarySimplex.sourceMap c (q ≫ p)).hom.toFunctor := ρ

/-- The actual initial row retains its geometric intermediate and normalized endpoint. -/
theorem rectangle_initial_row (i : Fin 3) :
    preRectangleNodes p q p' q' a b c hp hq F P ρ (initialIndex i) =
      preBinaryNodes F P c (q ≫ p) (rectangleInitialReference p q c F P ρ) i := by
  have hm (j : Fin 3) :
      (preRectangleNodes p q p' q' a b c hp hq F P ρ (initialIndex j)).1 =
      (preBinaryNodes F P c (q ≫ p) (rectangleInitialReference p q c F P ρ) j).1 := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    fin_cases j <;> rfl
  fin_cases i
  · exact Sigma.ext (hm 0) (heq_of_eq rfl)
  · exact Sigma.ext (hm 1) (heq_of_eq rfl)
  · exact Sigma.ext (hm 2) (heq_of_eq rfl)

/-- The original total-square equality transports the actual outer source comparison. -/
def rectangleOuterReference :
    F.hom.toFunctor ≅ (P ≫ BoundedFlatPerfectBinarySimplex.sourceMap
      (q' ≫ p') a).hom.toFunctor :=
  ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (eqToIso (lastRightFunctorEq p q p' q' a b c hp hq))

/-- The actual outer row retains its original equality transport and normalization. -/
theorem rectangle_outer_row (i : Fin 3) :
    preRectangleNodes p q p' q' a b c hp hq F P ρ (outerIndex i) =
      preBinaryNodes F P (q' ≫ p') a (rectangleOuterReference p q p' q' a b c hp hq F P ρ) i := by
  have hm (j : Fin 2) :
      (preRectangleNodes p q p' q' a b c hp hq F P ρ (outerIndex j.succ)).1 =
      (preBinaryNodes F P (q' ≫ p') a
        (rectangleOuterReference p q p' q' a b c hp hq F P ρ) j.succ).1 := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    fin_cases j <;> rfl
  fin_cases i
  · exact preSource_transport F P (lastRightFunctorEq p q p' q' a b c hp hq) ρ
  · apply Sigma.ext (hm 0)
    apply heq_of_eq
    change ρ ≪≫ isoWhiskerLeft P.hom.toFunctor
        (BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
          BoundedFlatPerfectSplitTripleSimplex.rightFirstGeometric q' p' a) =
      rectangleOuterReference p q p' q' a b c hp hq F P ρ ≪≫
        isoWhiskerLeft P.hom.toFunctor (BoundedFlatPerfectBinarySimplex.first (q' ≫ p') a)
    rw [lastRightRawReference, rectangleOuterReference, isoWhiskerLeft_trans, Iso.trans_assoc]
  · apply Sigma.ext (hm 1)
    apply heq_of_eq
    change ρ ≪≫ isoWhiskerLeft P.hom.toFunctor
        (BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
          BoundedFlatPerfectTripleSimplex.rightFirst q' p' a) =
      rectangleOuterReference p q p' q' a b c hp hq F P ρ ≪≫
        isoWhiskerLeft P.hom.toFunctor (BoundedFlatPerfectBinarySimplex.total (q' ≫ p') a)
    rw [lastRightNormalizedReference, rectangleOuterReference,
      isoWhiskerLeft_trans, Iso.trans_assoc]

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectRectangleInitialBinaryRow

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.MixedTransformation
public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedMixedHomotopy
public import Colib.CategoryTheory.Waldhausen.Additivity.SubdivisionZeroVertex

/-! Implementation provenance: `Quillen/Waldhausen/Additivity/MixedTransformationSquare.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, hypotheses, universes,
whole faces and chosen-zero surfaces are preserved. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SSet SSet.MixedOrdinalCylinder
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G H F' G' H' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')
  (ηF : F ⟶ F') (ηG : G ⟶ G') (haη : a ≫ ηG = ηF ≫ a')

private theorem normalizedPushoutApp_heq {f g : Arrow C} (h : f = g) :
    HEq ((normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app f)
      ((normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app g) := by
  subst g
  rfl

/-- The actual pushout transformation on the unchanged identity-interval family. -/
def normalizedIdentityTransformationFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((bisimplicialSSet V).obj n).obj m) :
    (((normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration).app n).app m A).1 ⟶
      (((normalizedIdentityMap V W a' hs'.exactF hs'.exactG hs'.cofibration).app n).app m A).1 :=
  Functor.whiskerLeft (intervalArrows (𝟙 n.unop) (𝟙 n.unop) (fun _ ↦ le_rfl) A.1)
    (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')

/-- Every component preserves the actual identity Arrow under reindexing. -/
theorem normalizedIdentityTransformationFamily_reindex {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n') (A : (SSet.diagonalSSet (bisimplicialSSet V)).obj n)
    (x : Grid₂ n'.unop n'.unop) :
    HEq ((normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη n' n'
        ((SSet.diagonalSSet (bisimplicialSSet V)).map α A)).app x)
      ((normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη n n A).app
        ((gridMap₂ α.unop α.unop).obj x)) := by
  apply normalizedPushoutApp_heq V W a a' b b' hs hs' ηF ηG haη
  rfl

/-- The actual pushout transformation on the unchanged separated-half family. -/
def normalizedSeparatedTransformationFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m) :
    (((normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration).app n).app m A).1 ⟶
      (((normalizedSeparatedMap V W a' hs'.exactF hs'.exactG hs'.cofibration).app n).app m A).1 :=
  Functor.whiskerLeft
    (intervalArrows (SSet.OrdinalJoin.left n.unop n.unop) (SSet.OrdinalJoin.right n.unop n.unop)
      (left_le_right n.unop) A.1)
    (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')

/-- The separated family retains the original subdivision and actual Arrow reindexing. -/
theorem normalizedSeparatedTransformationFamily_reindex {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n')
    (A : (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)).obj n)
    (x : Grid₂ n'.unop n'.unop) :
    HEq ((normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη n' n'
        ((SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)).map α A)).app x)
      ((normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη n n A).app
        ((gridMap₂ α.unop α.unop).obj x)) := by
  apply normalizedPushoutApp_heq V W a a' b b' hs hs' ηF ηG haη
  exact (congrArg (fun T ↦ T.obj x)
    (separatedIntervalArrows_reindex α.unop α.unop A.1)).symm

variable (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X))

/-- The original weak-grid cylinder at the actual identity endpoint. -/
def normalizedIdentityTransformationHomotopy :
    SSet.Homotopy
      (SSet.diagonalMap (normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration))
      (SSet.diagonalMap (normalizedIdentityMap V W a' hs'.exactF hs'.exactG hs'.cofibration)) :=
  diagonalWeakGridHomotopy W _ _
    (normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (fun _n _m _A _x ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (normalizedIdentityTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)

/-- The original weak-grid cylinder at the actual separated endpoint. -/
def normalizedSeparatedTransformationHomotopy :
    SSet.Homotopy
      (SSet.diagonalMap (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration))
      (SSet.diagonalMap
        (normalizedSeparatedMap V W a' hs'.exactF hs'.exactG hs'.cofibration)) :=
  diagonalWeakGridHomotopy W _ _
    (normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (fun _n _m _A _x ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (normalizedSeparatedTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)

/-- Zero-cut restriction identifies the entire original transformation cylinder. -/
theorem normalizedMixedTransformationHomotopy_zero :
    SSet.diagonalMap (outerZeroSection (bisimplicialSSet V)) ▷ Δ[1] ≫
        (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h =
      (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h := by
  ext n z
  apply Subtype.ext
  exact congrArg
    (fun T ↦ nerveCylinderDiagram (Functor.whiskerLeft T
      (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')) z.2.down)
    (mixedIntervalArrows_zero z.1.1)

/-- One-cut restriction identifies the entire unchanged separated transformation cylinder. -/
theorem normalizedMixedTransformationHomotopy_one :
    SSet.diagonalMap (outerOneSection (bisimplicialSSet V)) ▷ Δ[1] ≫
        (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h =
      (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h := by
  ext n z
  apply Subtype.ext
  exact congrArg
    (fun T ↦ nerveCylinderDiagram (Functor.whiskerLeft T
      (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')) z.2.down)
    (mixedIntervalArrows_one z.1.1)

/-- The original minimum-cut cylinder on the actual subdivided source. -/
def mixedTransformationInputCylinder :
    SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1] ⟶
      SSet.diagonalSSet (outerCylinder (bisimplicialSSet V)) :=
  SSet.diagonalMap (outerOneSection (bisimplicialSSet V)) ▷ Δ[1] ≫
    (outerContraction (bisimplicialSSet V)).h

/-- The original minimum-cut zero face is horizontal restriction followed by the zero section. -/
theorem mixedTransformationInputCylinder_zero :
    SSet.ι₀ ≫ mixedTransformationInputCylinder V =
      SSet.diagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) ≫
        SSet.diagonalMap (outerZeroSection (bisimplicialSSet V)) := by
  simp only [mixedTransformationInputCylinder, SSet.ι₀_comp_assoc, SSet.Homotopy.h₀]
  change SSet.diagonalFunctor.map
    (outerOneSection (bisimplicialSSet V) ≫ outerProjection (bisimplicialSSet V) ≫
      outerZeroSection (bisimplicialSSet V)) = _
  rw [← Category.assoc, outerOneSection_projection]
  rfl

/-- The original minimum-cut one face is the unchanged one-section inclusion. -/
theorem mixedTransformationInputCylinder_one :
    SSet.ι₁ ≫ mixedTransformationInputCylinder V =
      SSet.diagonalMap (outerOneSection (bisimplicialSSet V)) := by
  simp only [mixedTransformationInputCylinder, SSet.ι₁_comp_assoc, SSet.Homotopy.h₁,
    Category.comp_id]

/-- The literal two-time middle square: mixed time first, then transformation time simplicially. -/
def normalizedMixedTransformationSquare :
    (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1]) ⊗ Δ[1] ⟶
      SSet.diagonalSSet (bisimplicialSSet W) :=
  mixedTransformationInputCylinder V ▷ Δ[1] ≫
    (normalizedMixedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h

/-- Transformation time zero is precisely the old original mixed deformation cylinder. -/
theorem normalizedMixedTransformationSquare_transformation_zero :
    SSet.ι₀ ≫ normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      (normalizedMixedEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration).h := by
  simp only [normalizedMixedTransformationSquare, SSet.ι₀_comp_assoc, SSet.Homotopy.h₀]
  rfl

/-- Transformation time one is precisely the primed original mixed deformation cylinder. -/
theorem normalizedMixedTransformationSquare_transformation_one :
    SSet.ι₁ ≫ normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      (normalizedMixedEndpointHomotopy V W a' hs'.exactF hs'.exactG hs'.cofibration).h := by
  simp only [normalizedMixedTransformationSquare, SSet.ι₁_comp_assoc, SSet.Homotopy.h₁]
  rfl

/-- Mixed time zero is the whole identity transformation cylinder on actual horizontal
restriction. -/
theorem normalizedMixedTransformationSquare_mixed_zero :
    (SSet.ι₀ ▷ Δ[1]) ≫
        normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      SSet.diagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) ▷
          Δ[1] ≫
        (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h := by
  rw [normalizedMixedTransformationSquare, ← Category.assoc, ← comp_whiskerRight,
    mixedTransformationInputCylinder_zero, comp_whiskerRight, Category.assoc,
    normalizedMixedTransformationHomotopy_zero]

/-- Mixed time one is the whole separated transformation cylinder on the original subdivision. -/
theorem normalizedMixedTransformationSquare_mixed_one :
    (SSet.ι₁ ▷ Δ[1]) ≫
        normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h := by
  rw [normalizedMixedTransformationSquare, ← Category.assoc, ← comp_whiskerRight,
    mixedTransformationInputCylinder_one, normalizedMixedTransformationHomotopy_one]

/-- Every cut and both independent simplicial times keep the original chosen zero. -/
theorem normalizedMixedTransformationSquare_fixed_zero :
    ((SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) ≫
        normalizedMixedTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      CartesianMonoidalCategory.fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) := by
  ext n z
  apply Subtype.ext
  exact normalizedMixedTransformation_nerveCylinder_zero V W a a' b b' hs hs' ηF ηG haη
    (minCut (oneCut n.unop) z.1.2.down) z.2.down


end CategoryTheory.Waldhausen.Additivity

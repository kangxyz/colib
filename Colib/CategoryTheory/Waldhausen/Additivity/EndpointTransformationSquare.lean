/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.MixedTransformationSquare
public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedEndpointHomotopies
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakGridSquare

/-! Implementation provenance: `Quillen/Waldhausen/Additivity/EndpointTransformationSquare.lean` at
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
  (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X))

/-- The exact rebased middle-functor transformation, on the original ordinary diagonal. -/
def normalizedMiddleTransformationHomotopy :
    SSet.Homotopy
      (SSet.diagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase))
      (SSet.diagonalMap (bisimplicialSSetMap V.cof V.weq hs'.exactG.rebase)) :=
  diagonalWeakGridHomotopy W _ _
    (fun _ _ A ↦ Functor.whiskerLeft A.1
      (normalizedWeakTransformation hs.exactG hs'.exactG ηG))
    (fun _ _ A x ↦ normalizedWeakTransformation_weak hs.exactG hs'.exactG ηG hηG (A.1.obj x))
    (fun {_ _} _ _ _ ↦ HEq.rfl)

/-- The whole unreversed identity-endpoint naturality square. -/
def normalizedIdentityEndpointTransformationSquare :
    (SSet.diagonalSSet (bisimplicialSSet V) ⊗ Δ[1]) ⊗ Δ[1] ⟶
      SSet.diagonalSSet (bisimplicialSSet W) :=
  weakGridFamilySquare W
    (normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase)
    (normalizedIdentityMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs'.exactG.rebase)
    (normalizedIdentityEndpointFamily V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (fun _ _ A ↦ Functor.whiskerLeft A.1
      (normalizedWeakTransformation hs.exactG hs'.exactG ηG))
    (fun n m A ↦ (normalizedPushoutTransformation_identityEndpointFamily
      W a a' ηF ηG haη b b' V hs hs' n m A).symm)
    (normalizedIdentityEndpointFamily_weak V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily_weak V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ A x ↦ normalizedWeakTransformation_weak hs.exactG hs'.exactG ηG hηG (A.1.obj x))
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a hs.exactF hs.exactG hs.cofibration ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a' hs'.exactF hs'.exactG hs'.cofibration ρ.unop ρ.unop A x).symm)
    (normalizedIdentityTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (fun {_ _} _ _ _ ↦ HEq.rfl)

/-- The entire transformation zero face retains its original weak-grid cylinder. -/
theorem normalizedIdentityEndpointTransformationSquare_transformation_zero :
    SSet.ι₀ ≫ normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
      =
      (normalizedIdentityEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration).h :=
  weakGridFamilySquare_vertical_zero W
    (normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase)
    (normalizedIdentityMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs'.exactG.rebase)
    (normalizedIdentityEndpointFamily V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (fun _ _ A ↦ Functor.whiskerLeft A.1
      (normalizedWeakTransformation hs.exactG hs'.exactG ηG))
    (fun n m A ↦ (normalizedPushoutTransformation_identityEndpointFamily
      W a a' ηF ηG haη b b' V hs hs' n m A).symm)
    (normalizedIdentityEndpointFamily_weak V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily_weak V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ A x ↦ normalizedWeakTransformation_weak hs.exactG hs'.exactG ηG hηG (A.1.obj x))
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a hs.exactF hs.exactG hs.cofibration ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a' hs'.exactF hs'.exactG hs'.cofibration ρ.unop ρ.unop A x).symm)
    (normalizedIdentityTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (fun {_ _} _ _ _ ↦ HEq.rfl)

/-- The entire transformation one face retains its original weak-grid cylinder. -/
theorem normalizedIdentityEndpointTransformationSquare_transformation_one :
    SSet.ι₁ ≫ normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG
      =
      (normalizedIdentityEndpointHomotopy V W a' hs'.exactF hs'.exactG hs'.cofibration).h :=
  weakGridFamilySquare_vertical_one W
    (normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase)
    (normalizedIdentityMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs'.exactG.rebase)
    (normalizedIdentityEndpointFamily V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (fun _ _ A ↦ Functor.whiskerLeft A.1
      (normalizedWeakTransformation hs.exactG hs'.exactG ηG))
    (fun n m A ↦ (normalizedPushoutTransformation_identityEndpointFamily
      W a a' ηF ηG haη b b' V hs hs' n m A).symm)
    (normalizedIdentityEndpointFamily_weak V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily_weak V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ A x ↦ normalizedWeakTransformation_weak hs.exactG hs'.exactG ηG hηG (A.1.obj x))
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a hs.exactF hs.exactG hs.cofibration ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a' hs'.exactF hs'.exactG hs'.cofibration ρ.unop ρ.unop A x).symm)
    (normalizedIdentityTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (fun {_ _} _ _ _ ↦ HEq.rfl)

/-- The entire endpoint zero face retains its original weak-grid cylinder. -/
theorem normalizedIdentityEndpointTransformationSquare_endpoint_zero :
    (SSet.ι₀ ▷ Δ[1]) ≫ normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG
      haη hηF hηG =
      (normalizedIdentityTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h :=
  weakGridFamilySquare_horizontal_zero W
    (normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase)
    (normalizedIdentityMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs'.exactG.rebase)
    (normalizedIdentityEndpointFamily V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (fun _ _ A ↦ Functor.whiskerLeft A.1
      (normalizedWeakTransformation hs.exactG hs'.exactG ηG))
    (fun n m A ↦ (normalizedPushoutTransformation_identityEndpointFamily
      W a a' ηF ηG haη b b' V hs hs' n m A).symm)
    (normalizedIdentityEndpointFamily_weak V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily_weak V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ A x ↦ normalizedWeakTransformation_weak hs.exactG hs'.exactG ηG hηG (A.1.obj x))
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a hs.exactF hs.exactG hs.cofibration ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a' hs'.exactF hs'.exactG hs'.cofibration ρ.unop ρ.unop A x).symm)
    (normalizedIdentityTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (fun {_ _} _ _ _ ↦ HEq.rfl)

/-- The entire endpoint one face retains its original weak-grid cylinder. -/
theorem normalizedIdentityEndpointTransformationSquare_endpoint_one :
    (SSet.ι₁ ▷ Δ[1]) ≫ normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG
      haη hηF hηG =
      (normalizedMiddleTransformationHomotopy V W a a' b b' hs hs' ηG hηG).h :=
  weakGridFamilySquare_horizontal_one W
    (normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase)
    (normalizedIdentityMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs'.exactG.rebase)
    (normalizedIdentityEndpointFamily V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (fun _ _ A ↦ Functor.whiskerLeft A.1
      (normalizedWeakTransformation hs.exactG hs'.exactG ηG))
    (fun n m A ↦ (normalizedPushoutTransformation_identityEndpointFamily
      W a a' ηF ηG haη b b' V hs hs' n m A).symm)
    (normalizedIdentityEndpointFamily_weak V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily_weak V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ A x ↦ normalizedWeakTransformation_weak hs.exactG hs'.exactG ηG hηG (A.1.obj x))
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a hs.exactF hs.exactG hs.cofibration ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a' hs'.exactF hs'.exactG hs'.cofibration ρ.unop ρ.unop A x).symm)
    (normalizedIdentityTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (fun {_ _} _ _ _ ↦ HEq.rfl)

/-- All four original zero grids fix the entire identity-endpoint square. -/
theorem normalizedIdentityEndpointTransformationSquare_fixed_zero :
    ((SSet.yonedaEquiv.symm (diagonalZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) ≫
        normalizedIdentityEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG =
      CartesianMonoidalCategory.fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) := by
  refine weakGridFamilySquare_fixed_vertex W
    (normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase)
    (normalizedIdentityMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (bisimplicialSSetMap V.cof V.weq hs'.exactG.rebase)
    (normalizedIdentityEndpointFamily V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedIdentityTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (fun _ _ A ↦ Functor.whiskerLeft A.1
      (normalizedWeakTransformation hs.exactG hs'.exactG ηG))
    (fun n m A ↦ (normalizedPushoutTransformation_identityEndpointFamily
      W a a' ηF ηG haη b b' V hs hs' n m A).symm)
    (normalizedIdentityEndpointFamily_weak V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedIdentityEndpointFamily_weak V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ A x ↦ normalizedWeakTransformation_weak hs.exactG hs'.exactG ηG hηG (A.1.obj x))
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a hs.exactF hs.exactG hs.cofibration ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedIdentityEndpointFamily_reindex_app
      V W a' hs'.exactF hs'.exactG hs'.cofibration ρ.unop ρ.unop A x).symm)
    (normalizedIdentityTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (fun {_ _} _ _ _ ↦ HEq.rfl)
    (diagonalZeroVertex V) ?_ ?_ ?_ ?_
  · intro n z p
    exact normalizedIntervalDiagram_zero_obj V W a hs.exactF hs.exactG hs.cofibration _ _ _ p
  · intro n z p
    exact CategoryTheory.rebaseFunctor_obj_base G V.zero W.zero ((hs.exactG.zero V.isZero).iso
      W.isZero)
  · intro n z p
    exact normalizedIntervalDiagram_zero_obj V W a' hs'.exactF hs'.exactG hs'.cofibration _ _ _ p
  · intro n z p
    exact CategoryTheory.rebaseFunctor_obj_base G' V.zero W.zero ((hs'.exactG.zero V.isZero).iso
      W.isZero)

variable [HasBinaryCoproducts D]
  (ηH : H ⟶ H') (hbη : b ≫ ηH = ηG ≫ b') (hηH : ∀ X, W.weq (ηH.app X))

private theorem normalizedSplitApp_heq {x y : C × C} (h : x = y) :
    HEq ((normalizedSplitEndpointTransformation W a a' ηF b b' ηH V hs hs').app x)
      ((normalizedSplitEndpointTransformation W a a' ηF b b' ηH V hs hs').app y) := by
  subst y
  rfl

/-- The actual separated pair transformation retains quotient-first order. -/
def normalizedSumTransformationFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m) :
    (((normalizedSumMap V W hs.exactH hs.exactF).app n).app m A).1 ⟶
      (((normalizedSumMap V W hs'.exactH hs'.exactF).app n).app m A).1 :=
  Functor.whiskerLeft (separatedPairGrid A.1)
    (normalizedSplitEndpointTransformation W a a' ηF b b' ηH V hs hs')

/-- The actual separated-pair restriction supplies the unchanged diagonal reindexing. -/
theorem normalizedSumTransformationFamily_reindex {n n' : SimplexCategoryᵒᵖ}
    (ρ : n ⟶ n')
    (A : (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)).obj n)
    (x : Grid₂ n'.unop n'.unop) :
    HEq ((normalizedSumTransformationFamily V W a a' b b' hs hs' ηF ηH n' n'
        ((SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)).map ρ A)).app x)
      ((normalizedSumTransformationFamily V W a a' b b' hs hs' ηF ηH n n A).app
        ((gridMap₂ ρ.unop ρ.unop).obj x)) := by
  apply normalizedSplitApp_heq V W a a' b b' hs hs' ηF ηH
  exact congrArg (fun T ↦ T.obj x) (separatedPairGrid_reindex ρ.unop ρ.unop A.1)

/-- The original weak-grid cylinder of the actual quotient-first normalized sum. -/
def normalizedSumTransformationHomotopy :
    SSet.Homotopy
      (SSet.diagonalMap (normalizedSumMap V W hs.exactH hs.exactF))
      (SSet.diagonalMap (normalizedSumMap V W hs'.exactH hs'.exactF)) :=
  diagonalWeakGridHomotopy W _ _
    (normalizedSumTransformationFamily V W a a' b b' hs hs' ηF ηH)
    (fun _ _ _ _ ↦
      normalizedSplitEndpointTransformation_weak W a a' ηF b b' ηH V hs hs' hηH hηF _)
    (normalizedSumTransformationFamily_reindex V W a a' b b' hs hs' ηF ηH)

/-- The whole unreversed separated-endpoint naturality square. -/
def normalizedSeparatedEndpointTransformationSquare :
    (SSet.diagonalSSet (SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V) ⊗ Δ[1]) ⊗ Δ[1] ⟶
      SSet.diagonalSSet (bisimplicialSSet W) :=
  weakGridFamilySquare W
    (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedSumMap V W hs.exactH hs.exactF)
    (normalizedSeparatedMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedSumMap V W hs'.exactH hs'.exactF)
    (normalizedSeparatedEndpointFamily V W a b hs)
    (normalizedSeparatedEndpointFamily V W a' b' hs')
    (normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily V W a a' b b' hs hs' ηF ηH)
    (fun n m A ↦ (normalizedPushoutTransformation_separatedEndpointFamily
      W a a' ηF ηG haη b b' ηH hbη V hs hs' n m A).symm)
    (normalizedSeparatedEndpointFamily_weak V W a b hs)
    (normalizedSeparatedEndpointFamily_weak V W a' b' hs')
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ _ _ ↦
      normalizedSplitEndpointTransformation_weak W a a' ηF b b' ηH V hs hs' hηH hηF _)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a b hs ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a' b' hs' ρ.unop ρ.unop A x).symm)
    (normalizedSeparatedTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily_reindex V W a a' b b' hs hs' ηF ηH)

/-- The entire transformation zero face retains its original weak-grid cylinder. -/
theorem normalizedSeparatedEndpointTransformationSquare_transformation_zero :
    SSet.ι₀ ≫ normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH =
      (normalizedSeparatedEndpointHomotopy V W a b hs).h :=
  weakGridFamilySquare_vertical_zero W
    (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedSumMap V W hs.exactH hs.exactF)
    (normalizedSeparatedMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedSumMap V W hs'.exactH hs'.exactF)
    (normalizedSeparatedEndpointFamily V W a b hs)
    (normalizedSeparatedEndpointFamily V W a' b' hs')
    (normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily V W a a' b b' hs hs' ηF ηH)
    (fun n m A ↦ (normalizedPushoutTransformation_separatedEndpointFamily
      W a a' ηF ηG haη b b' ηH hbη V hs hs' n m A).symm)
    (normalizedSeparatedEndpointFamily_weak V W a b hs)
    (normalizedSeparatedEndpointFamily_weak V W a' b' hs')
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ _ _ ↦
      normalizedSplitEndpointTransformation_weak W a a' ηF b b' ηH V hs hs' hηH hηF _)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a b hs ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a' b' hs' ρ.unop ρ.unop A x).symm)
    (normalizedSeparatedTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily_reindex V W a a' b b' hs hs' ηF ηH)

/-- The entire transformation one face retains its original weak-grid cylinder. -/
theorem normalizedSeparatedEndpointTransformationSquare_transformation_one :
    SSet.ι₁ ≫ normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF
      hηG ηH hbη hηH =
      (normalizedSeparatedEndpointHomotopy V W a' b' hs').h :=
  weakGridFamilySquare_vertical_one W
    (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedSumMap V W hs.exactH hs.exactF)
    (normalizedSeparatedMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedSumMap V W hs'.exactH hs'.exactF)
    (normalizedSeparatedEndpointFamily V W a b hs)
    (normalizedSeparatedEndpointFamily V W a' b' hs')
    (normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily V W a a' b b' hs hs' ηF ηH)
    (fun n m A ↦ (normalizedPushoutTransformation_separatedEndpointFamily
      W a a' ηF ηG haη b b' ηH hbη V hs hs' n m A).symm)
    (normalizedSeparatedEndpointFamily_weak V W a b hs)
    (normalizedSeparatedEndpointFamily_weak V W a' b' hs')
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ _ _ ↦
      normalizedSplitEndpointTransformation_weak W a a' ηF b b' ηH V hs hs' hηH hηF _)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a b hs ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a' b' hs' ρ.unop ρ.unop A x).symm)
    (normalizedSeparatedTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily_reindex V W a a' b b' hs hs' ηF ηH)

/-- The entire endpoint zero face retains its original weak-grid cylinder. -/
theorem normalizedSeparatedEndpointTransformationSquare_endpoint_zero :
    (SSet.ι₀ ▷ Δ[1]) ≫ normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG
      haη hηF hηG ηH hbη hηH =
      (normalizedSeparatedTransformationHomotopy V W a a' b b' hs hs' ηF ηG haη hηF hηG).h :=
  weakGridFamilySquare_horizontal_zero W
    (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedSumMap V W hs.exactH hs.exactF)
    (normalizedSeparatedMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedSumMap V W hs'.exactH hs'.exactF)
    (normalizedSeparatedEndpointFamily V W a b hs)
    (normalizedSeparatedEndpointFamily V W a' b' hs')
    (normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily V W a a' b b' hs hs' ηF ηH)
    (fun n m A ↦ (normalizedPushoutTransformation_separatedEndpointFamily
      W a a' ηF ηG haη b b' ηH hbη V hs hs' n m A).symm)
    (normalizedSeparatedEndpointFamily_weak V W a b hs)
    (normalizedSeparatedEndpointFamily_weak V W a' b' hs')
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ _ _ ↦
      normalizedSplitEndpointTransformation_weak W a a' ηF b b' ηH V hs hs' hηH hηF _)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a b hs ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a' b' hs' ρ.unop ρ.unop A x).symm)
    (normalizedSeparatedTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily_reindex V W a a' b b' hs hs' ηF ηH)

/-- The entire endpoint one face retains its original weak-grid cylinder. -/
theorem normalizedSeparatedEndpointTransformationSquare_endpoint_one :
    (SSet.ι₁ ▷ Δ[1]) ≫ normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG
      haη hηF hηG ηH hbη hηH =
      (normalizedSumTransformationHomotopy V W a a' b b' hs hs' ηF hηF ηH hηH).h :=
  weakGridFamilySquare_horizontal_one W
    (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedSumMap V W hs.exactH hs.exactF)
    (normalizedSeparatedMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedSumMap V W hs'.exactH hs'.exactF)
    (normalizedSeparatedEndpointFamily V W a b hs)
    (normalizedSeparatedEndpointFamily V W a' b' hs')
    (normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily V W a a' b b' hs hs' ηF ηH)
    (fun n m A ↦ (normalizedPushoutTransformation_separatedEndpointFamily
      W a a' ηF ηG haη b b' ηH hbη V hs hs' n m A).symm)
    (normalizedSeparatedEndpointFamily_weak V W a b hs)
    (normalizedSeparatedEndpointFamily_weak V W a' b' hs')
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ _ _ ↦
      normalizedSplitEndpointTransformation_weak W a a' ηF b b' ηH V hs hs' hηH hηF _)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a b hs ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a' b' hs' ρ.unop ρ.unop A x).symm)
    (normalizedSeparatedTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily_reindex V W a a' b b' hs hs' ηF ηH)

/-- All four original zero grids fix the entire separated-endpoint square. -/
theorem normalizedSeparatedEndpointTransformationSquare_fixed_zero :
    ((SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) ≫
        normalizedSeparatedEndpointTransformationSquare V W a a' b b' hs hs' ηF ηG haη hηF hηG ηH
          hbη hηH =
      CartesianMonoidalCategory.fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) := by
  refine weakGridFamilySquare_fixed_vertex W
    (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration)
    (normalizedSumMap V W hs.exactH hs.exactF)
    (normalizedSeparatedMap V W a' hs'.exactF hs'.exactG hs'.cofibration)
    (normalizedSumMap V W hs'.exactH hs'.exactF)
    (normalizedSeparatedEndpointFamily V W a b hs)
    (normalizedSeparatedEndpointFamily V W a' b' hs')
    (normalizedSeparatedTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily V W a a' b b' hs hs' ηF ηH)
    (fun n m A ↦ (normalizedPushoutTransformation_separatedEndpointFamily
      W a a' ηF ηG haη b b' ηH hbη V hs hs' n m A).symm)
    (normalizedSeparatedEndpointFamily_weak V W a b hs)
    (normalizedSeparatedEndpointFamily_weak V W a' b' hs')
    (fun _ _ _ _ ↦
      normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _)
    (fun _ _ _ _ ↦
      normalizedSplitEndpointTransformation_weak W a a' ηF b b' ηH V hs hs' hηH hηF _)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a b hs ρ.unop ρ.unop A x).symm)
    (fun {_ _} ρ A x ↦ (normalizedSeparatedEndpointFamily_reindex_app
      V W a' b' hs' ρ.unop ρ.unop A x).symm)
    (normalizedSeparatedTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)
    (normalizedSumTransformationFamily_reindex V W a a' b b' hs hs' ηF ηH)
    (subdivisionZeroVertex V) ?_ ?_ ?_ ?_
  · intro n z p
    exact normalizedIntervalDiagram_zero_obj V W a hs.exactF hs.exactG hs.cofibration _ _ _ p
  · intro n z p
    exact normalizedSumGrid_zero_obj V W hs.exactH hs.exactF p
  · intro n z p
    exact normalizedIntervalDiagram_zero_obj V W a' hs'.exactF hs'.exactG hs'.cofibration _ _ _ p
  · intro n z p
    exact normalizedSumGrid_zero_obj V W hs'.exactH hs'.exactF p


end CategoryTheory.Waldhausen.Additivity

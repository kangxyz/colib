/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Generators
public import Colib.CategoryTheory.Sites.Simplicial.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Actual Nisnevich square generators on site fibers

The strict pointed square map is compared with the freely pointed constant
simplicial lift of its ordinary type-valued presheaf map. Constant simplicial
lift and free pointing preserve the defining pushout. The native fiber
comparison and coproduct comparison then show that every site fiber sends
the actual geometric generator to a simplicial-set isomorphism.

Only ordinary type-valued sheafification is assumed. There is no use of an
enough-points theorem or a local model-category comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C]

/-- The constant simplicial lift of a presheaf, with a freely adjoined point. -/
def discretePointedPresheafFunctor : (Cᵒᵖ ⥤ Type w) ⥤ PointedSimplicialPresheaf.{w} C :=
  (Functor.whiskeringRight Cᵒᵖ (Type w) SSet.{w}).obj
      (Functor.const SimplexCategoryᵒᵖ) ⋙ free C

instance : PreservesFiniteColimits (discretePointedPresheafFunctor.{w} C) where
  preservesFiniteColimits K _ _ := by
    let : (free.{w} C).IsLeftAdjoint := (freeForgetAdjunction C).isLeftAdjoint
    dsimp [discretePointedPresheafFunctor]
    infer_instance

variable {J : GrothendieckTopology C}

/-- Free pointing preserves an actual fiber isomorphism, through the native
binary-coproduct comparison for the fiber functor. -/
theorem isIso_fiberAtPoint_free_map (Φ : J.Point.{w})
    {P Q : Cᵒᵖ ⥤ SSet.{w}} (f : P ⟶ Q) [IsIso (Φ.presheafFiber.map f)] :
    IsIso ((fiberAtPoint C Φ).map ((free C).map f)) := by
  let T : Cᵒᵖ ⥤ SSet.{w} := ⊤_ _
  change IsIso (Φ.presheafFiber.map (coprod.map f (𝟙 T)))
  have h := coprodComparison_natural (Φ.presheafFiber (A := SSet.{w})) f (𝟙 T)
  let : IsIso (coprodComparison Φ.presheafFiber P T ≫
      Φ.presheafFiber.map (coprod.map f (𝟙 T))) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (coprodComparison Φ.presheafFiber P T) _

/-- Constant simplicial lift followed by free pointing sends the native
type-valued sheafification class to isomorphisms on actual fibers. -/
theorem isIso_fiberAtPoint_discretePointed_map_of_W [LocallySmall.{w} C]
    (Φ : J.Point.{w}) {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q) (hf : J.W f) :
    IsIso ((fiberAtPoint C Φ).map ((discretePointedPresheafFunctor C).map f)) := by
  let K : Type w ⥤ SSet.{w} := Functor.const SimplexCategoryᵒᵖ
  let : IsIso ((Φ.presheafFiber (A := Type w)).map f) :=
    Φ.W_isInvertedBy_presheafFiber f hf
  let : IsIso (Φ.presheafFiber.map (Functor.whiskerRight f K)) := by
    apply (NatIso.isIso_map_iff (Φ.presheafFiberCompIso K) f).2
    change IsIso (K.map ((Φ.presheafFiber (A := Type w)).map f))
    infer_instance
  exact isIso_fiberAtPoint_free_map C Φ (Functor.whiskerRight f K)

end CategoryTheory.PointedSimplicialPresheaf

namespace AlgebraicGeometry.MotivicHomotopy

open Scheme Scheme.SmoothSite CategoryTheory.PointedSimplicialPresheaf

variable (S : Scheme.{u})

/-- The actual strict pointed pushout is the freely pointed constant simplicial
lift of the ordinary presheaf pushout. -/
def nisnevichSquareDiscretePushoutIso (Q : NisnevichSquare S) :
    squarePushout (SmoothSite S) Q.val ≅
      (discretePointedPresheafFunctor (SmoothSite S)).obj
        (pushout (CategoryTheory.yoneda.map Q.val.f₁₂)
          (CategoryTheory.yoneda.map Q.val.f₁₃)) :=
  (squarePushout_isPushout (SmoothSite S) Q.val).isoIsPushout _ _
    ((IsPushout.of_hasPushout (CategoryTheory.yoneda.map Q.val.f₁₂)
      (CategoryTheory.yoneda.map Q.val.f₁₃)).map
        (discretePointedPresheafFunctor (SmoothSite S)))

/-- The comparison retains the original top-right leg. -/
@[reassoc (attr := simp)]
theorem squarePushoutInl_nisnevichSquareDiscretePushoutIso (Q : NisnevichSquare S) :
    squarePushoutInl (SmoothSite S) Q.val ≫ (nisnevichSquareDiscretePushoutIso S Q).hom =
      (discretePointedPresheafFunctor (SmoothSite S)).map (pushout.inl _ _) :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

/-- The comparison retains the original bottom-left leg. -/
@[reassoc (attr := simp)]
theorem squarePushoutInr_nisnevichSquareDiscretePushoutIso (Q : NisnevichSquare S) :
    squarePushoutInr (SmoothSite S) Q.val ≫ (nisnevichSquareDiscretePushoutIso S Q).hom =
      (discretePointedPresheafFunctor (SmoothSite S)).map (pushout.inr _ _) :=
  IsPushout.inr_isoIsPushout_hom _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The comparison identifies the actual generator, including its map to the fourth corner. -/
@[reassoc]
theorem nisnevichSquareDiscretePushoutIso_hom_map (Q : NisnevichSquare S) :
    (nisnevichSquareDiscretePushoutIso S Q).hom ≫
        (discretePointedPresheafFunctor (SmoothSite S)).map (nisnevichPresheafSquareMap Q) =
      nisnevichSquareMap S Q := by
  apply pushout.hom_ext
  · change squarePushoutInl (SmoothSite S) Q.val ≫ _ =
      squarePushoutInl (SmoothSite S) Q.val ≫ _
    rw [← Category.assoc, squarePushoutInl_nisnevichSquareDiscretePushoutIso,
      ← Functor.map_comp, nisnevichSquareMap_inl]
    exact congrArg (discretePointedPresheafFunctor (SmoothSite S)).map
      (pushout.inl_desc _ _ _)
  · change squarePushoutInr (SmoothSite S) Q.val ≫ _ =
      squarePushoutInr (SmoothSite S) Q.val ≫ _
    rw [← Category.assoc, squarePushoutInr_nisnevichSquareDiscretePushoutIso,
      ← Functor.map_comp, nisnevichSquareMap_inr]
    exact congrArg (discretePointedPresheafFunctor (SmoothSite S)).map
      (pushout.inr_desc _ _ _)

variable [HasWeakSheafify (nisnevichTopology S) (Type u)]

set_option backward.isDefEq.respectTransparency false in
/-- Every actual Nisnevich site point sends the geometric square generator
to a simplicial-set isomorphism. -/
theorem isIso_fiberAtPoint_nisnevichSquareMap
    (Φ : (nisnevichTopology S).Point.{u}) (Q : NisnevichSquare S) :
    IsIso ((fiberAtPoint (SmoothSite S) Φ).map (nisnevichSquareMap S Q)) := by
  have hf : (nisnevichTopology S).W (nisnevichPresheafSquareMap Q) :=
    ((nisnevichTopology S).W_iff _).2 (isIso_sheafify_nisnevichPresheafSquareMap Q)
  let : IsIso ((fiberAtPoint (SmoothSite S) Φ).map
      ((discretePointedPresheafFunctor (SmoothSite S)).map (nisnevichPresheafSquareMap Q))) :=
    isIso_fiberAtPoint_discretePointed_map_of_W (SmoothSite S) Φ _ hf
  rw [← nisnevichSquareDiscretePushoutIso_hom_map S Q, Functor.map_comp]
  infer_instance

/-- Each actual geometric square generator belongs to the selected stalkwise weak class. -/
theorem stalkwiseWeakEquivalences_nisnevichSquareMap (Q : NisnevichSquare S) :
    stalkwiseWeakEquivalences (SmoothSite S) (nisnevichTopology S)
      (nisnevichSquareMap S Q) := by
  intro Φ
  let : IsIso ((fiberAtPoint (SmoothSite S) Φ).map (nisnevichSquareMap S Q)) :=
    isIso_fiberAtPoint_nisnevichSquareMap S Φ Q
  exact SSet.realizationWeakEquivalences_of_isIso _

/-- The raw geometric Nisnevich family is contained in the actual stalkwise weak class. -/
theorem nisnevichSquareMaps_le_stalkwiseWeakEquivalences :
    nisnevichSquareMaps S ≤ stalkwiseWeakEquivalences (SmoothSite S) (nisnevichTopology S) := by
  rintro _ _ _ ⟨Q⟩
  exact stalkwiseWeakEquivalences_nisnevichSquareMap S Q

end AlgebraicGeometry.MotivicHomotopy

attribute [colib_tag "COL-0391"]
  AlgebraicGeometry.MotivicHomotopy.isIso_fiberAtPoint_nisnevichSquareMap
  AlgebraicGeometry.MotivicHomotopy.nisnevichSquareMaps_le_stalkwiseWeakEquivalences

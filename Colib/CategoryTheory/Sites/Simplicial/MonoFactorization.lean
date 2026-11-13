/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.BoundedMonoGenerators
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseTrivialComposition
import Colib.CategoryTheory.Limits.UnderCoproductPushout
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# Factorization by the small family of pointed monomorphisms

Coproducts, pushouts and transfinite attachments of the bounded
generators are monomorphisms. The native factorization therefore has
a monomorphism on the left and a map lifting against all
monomorphisms on the right.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MorphismProperty Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C]

instance monomorphisms_isStableUnderCobaseChange :
    (monomorphisms (PointedSimplicialPresheaf.{w} C)).IsStableUnderCobaseChange where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    let : Mono f := hf
    let W := monomorphisms (Cᵒᵖ ⥤ SSet.{w})
    let : W.IsStableUnderCobaseChange := by
      change (monomorphisms (Cᵒᵖ ⥤ SSet.{w})).IsStableUnderCobaseChange
      rw [← functorCategory_monomorphisms]
      infer_instance
    let : Mono f'.right := W.of_isPushout (sq.map (forget.{w} C)) (Under.mono_right_of_mono f)
    exact Under.mono_of_mono_right f'

/-- Pointed coproducts of monomorphisms are monomorphisms on the actual underlying presheaves. -/
theorem mono_sigmaMap {ι : Type w} {X Y : ι → PointedSimplicialPresheaf.{w} C}
    [HasCoproduct X] [HasCoproduct Y] (f : ∀ i, X i ⟶ Y i) (h : ∀ i, Mono (f i)) :
    Mono (Limits.Sigma.map f) := by
  let : HasCoproducts.{w} (Type w) := inferInstance
  let : HasCoproducts.{w} SSet.{w} := inferInstance
  let hPresheaf : HasCoproducts.{w} (Cᵒᵖ ⥤ SSet.{w}) := fun J => by
    let : HasColimitsOfShape (Discrete J) SSet.{w} := inferInstance
    exact CategoryTheory.Limits.functorCategoryHasColimitsOfShape
  let : HasCoproducts.{w} (Cᵒᵖ ⥤ SSet.{w}) := hPresheaf
  let g (i : ι) := (f i).right
  let : ∀ i, Mono (g i) := fun i => by
    let : Mono (f i) := h i
    exact Under.mono_right_of_mono _
  let : Mono (Limits.Sigma.map g) := inferInstance
  have sq : IsPushout (Limits.Sigma.map g) (Under.coproductRightMap X)
      (Under.coproductRightMap Y) (Limits.Sigma.map f).right := Under.sigmaMap_right_isPushout f
  let W := monomorphisms (Cᵒᵖ ⥤ SSet.{w})
  let : W.IsStableUnderCobaseChange := by
    change (monomorphisms (Cᵒᵖ ⥤ SSet.{w})).IsStableUnderCobaseChange
    rw [← functorCategory_monomorphisms]
    infer_instance
  let : Mono (Limits.Sigma.map f).right := W.of_isPushout sq.flip
    (inferInstanceAs (Mono (Limits.Sigma.map g)))
  exact Under.mono_of_mono_right _

instance monomorphisms_isStableUnderCoproducts :
    (monomorphisms (PointedSimplicialPresheaf.{w} C)).IsStableUnderCoproducts.{w} where
  isStableUnderCoproductsOfShape ι :=
    IsStableUnderCoproductsOfShape.mk _ ι (fun _ _ _ _ f hf => mono_sigmaMap C f hf)

instance monomorphisms_isStableUnderTransfiniteCompositionOfShape
    (I : Type w) [LinearOrder I] [SuccOrder I] [OrderBot I] [WellFoundedLT I] :
    (monomorphisms (PointedSimplicialPresheaf.{w} C)).IsStableUnderTransfiniteCompositionOfShape I
    where
  le X Y f hf := by
    obtain ⟨t⟩ := hf
    let F := forget.{w} C
    let : PreservesWellOrderContinuousOfShape I F := ⟨fun i hi => by
      let : Nonempty (Set.Iio i) := ⟨⟨⊥, Order.IsSuccLimit.bot_lt hi⟩⟩
      let : IsConnected (Set.Iio i) := IsFiltered.isConnected _
      infer_instance⟩
    let : IsConnected I := IsFiltered.isConnected _
    let W := monomorphisms (Cᵒᵖ ⥤ SSet.{w})
    let : W.IsStableUnderTransfiniteCompositionOfShape I := inferInstanceAs
      ((monomorphisms (Cᵒᵖ ⥤ SSet.{w})).IsStableUnderTransfiniteCompositionOfShape I)
    have tF : (W.inverseImage F).TransfiniteCompositionOfShape I f :=
      t.ofLE (fun _ _ g hg => by
        let : Mono g := hg
        exact Under.mono_right_of_mono g)
    let : Mono f.right := W.transfiniteCompositionsOfShape_le I _ ⟨tF.map⟩
    exact Under.mono_of_mono_right f

/-- Every pointed simplicial presheaf map factors through a monomorphism
followed by a map lifting against all monomorphisms. -/
theorem hasFactorization_monomorphisms_rlp :
    let W := monomorphisms (PointedSimplicialPresheaf.{max u v} C)
    HasFactorization W W.rlp := by
  let W := monomorphisms (PointedSimplicialPresheaf.{max u v} C)
  let T := Σ q : Cᵒᵖ × SimplexCategoryᵒᵖ, Σ r : Cᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r
  obtain ⟨κ, _, hT⟩ := HasCardinalLT.exists_regular_cardinal.{max u v} T
  let I := boundedMonoGenerators C κ
  have hI : I ≤ W := boundedMonoGenerators_le C κ
  have hEq : I.rlp = W.rlp := rlp_boundedMonoGenerators_eq C κ
    (fun q => hT.of_injective (fun s : Σ r : Cᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r =>
      (⟨q, s⟩ : T)) (by intro _ _ e; exact eq_of_heq (Sigma.mk.inj_iff.1 e).2))
  let hSOA := hasSmallObjectArgument_boundedMonoGenerators C κ
  obtain ⟨ν, hν, hbot, hsoa⟩ := hSOA.exists_cardinal
  let : Fact ν.IsRegular := hν
  let : OrderBot ν.ord.ToType := hbot
  let : I.IsCardinalForSmallObjectArgument ν := hsoa
  constructor
  intro X Y f
  have hP : (coproducts.{max u v} I).pushouts ≤ W :=
    (pushouts_le_iff (Q := W)).2 ((coproducts_le_iff (Q := W)).2 hI)
  let i := SmallObject.ιObj I ν f
  let p := SmallObject.πObj I ν f
  have hi : W i := W.transfiniteCompositionsOfShape_le ν.ord.ToType i
    (transfiniteCompositionsOfShape_monotone ν.ord.ToType hP i
      (SmallObject.transfiniteCompositionsOfShape_ιObj I ν f))
  exact ⟨⟨_, i, p, SmallObject.ιObj_πObj I ν f, hi, hEq ▸ SmallObject.rlp_πObj I ν f⟩⟩

end CategoryTheory.PointedSimplicialPresheaf

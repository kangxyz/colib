/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalCellWeakEquivalence
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Interval-local fibrant replacement

The small family consists of the original bounded stalkwise trivial maps
and free pointings of the pushout-products with a point of the parameter.
The right map tests stalkwise fibrancy and interval locality. The left map
satisfies the two extension tests into every fibrant local target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MorphismProperty MonoidalCategory Opposite
open CategoryTheory.SimplicialSubpresheaf

universe v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  {I : Cᵒᵖ ⥤ SSet.{max u v}} (s : (⊤_ (Cᵒᵖ ⥤ SSet.{max u v})) ⟶ I)
  (κ : Cardinal.{max u v})

attribute [local instance] Functor.functorCategoryMonoidalClosed

private def boundedIntervalGenerator
    (q : BoundedTrivialArrow C J κ ⊕ BoundedMonoArrow C κ) : Arrow
      (PointedSimplicialPresheaf.{max u v} C) :=
  match q with
  | .inl q => Arrow.mk ((free C).map q.val.2.2)
  | .inr q => Arrow.mk ((free C).map (Arrow.mk s □ Arrow.mk q.val.2.2).hom)

private def boundedIntervalGenerators : MorphismProperty
    (PointedSimplicialPresheaf.{max u v} C) :=
  MorphismProperty.ofHoms (fun q => (boundedIntervalGenerator C J s κ q).hom)

private theorem boundedIntervalGenerators_le :
    boundedIntervalGenerators C J s κ ≤ intervalLocalExtension (I := I) J := by
  rintro A B f ⟨q⟩
  rcases q with q | q
  · exact stalkwiseTrivialMonomorphisms_le_intervalLocalExtension J _
      (boundedTrivialGenerators_le C J κ _ ⟨q⟩)
  · let : Mono q.val.2.2 := q.property
    exact intervalLocalExtension_free_intervalPoint_pushoutProduct J s q.val.2.2

private theorem boundedTrivialGenerators_le_boundedIntervalGenerators :
    boundedTrivialGenerators C J κ ≤ boundedIntervalGenerators C J s κ := by
  rintro A B f ⟨q⟩
  exact ⟨Sum.inl q⟩

private theorem rlp_exponentialPre_of_boundedIntervalGenerators
    {E : PointedSimplicialPresheaf.{max u v} C}
    (hE : (boundedIntervalGenerators C J s κ).rlp (toPoint C E))
    (hC : ∀ q : Cᵒᵖ × SimplexCategoryᵒᵖ,
      HasCardinalLT (Σ r : Cᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ) :
    (monomorphisms (PointedSimplicialPresheaf.{max u v} C)).rlp
      (Under.constantPointExponentialPre s E) := by
  rw [← rlp_boundedMonoGenerators_eq C κ hC]
  intro A B f hf
  obtain ⟨q⟩ := hf
  let g := q.val.2.2
  have hq : boundedIntervalGenerators C J s κ ((free C).map (Arrow.mk s □ Arrow.mk g).hom) :=
    ⟨Sum.inr q⟩
  have h := hasLiftingProperty_underlying_toPoint_of_free (C := C) _ (hE _ hq)
  have hl : HasLiftingProperty g (Under.constantPointExponentialPre s E).right :=
    (Arrow.PushoutProduct.hasLiftingProperty_mk_isTerminal_iff
      (f := s) (g := g) terminalIsTerminal).1 h
  exact ((freeForgetAdjunction C).hasLiftingProperty_iff g
    (Under.constantPointExponentialPre s E)).2 hl

variable [J.HasEnoughPoints.{max u v}]

include s in
/-- Every original pointed simplicial presheaf has an interval weak
map to a stalkwise fibrant representative of an interval-local object. -/
@[colib_ref "Jardine2000MotivicSpectra" "Section 1.2, equation (1.1), pp. 453–454" "adaptation"
  "Pointed lifting tests at the chosen interval point and native small object factorization"]
theorem exists_intervalLocalFibrantReplacement (X : PointedSimplicialPresheaf.{max u v} C) :
    ∃ (Y : PointedSimplicialPresheaf.{max u v} C) (i : X ⟶ Y),
      intervalWeakEquivalences C J I i ∧
        IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj Y) := by
  obtain ⟨F, hSmall, hF⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty J
  let : ObjectProperty.Small.{max u v} F := hSmall
  obtain ⟨ν, hReg, hν, hFν, hC, hPoint⟩ := exists_regular_cardinal_bounds (F := F)
  let : Fact ν.IsRegular := hReg
  let K := boundedIntervalGenerators C J s ν
  let W := intervalLocalExtension (I := I) J
  let : LocallySmall.{max u v} (PointedSimplicialPresheaf.{max u v} C) :=
    CategoryTheory.locallySmall_self _
  let : HasSmallObjectArgument.{max u v} K :=
    hasSmallObjectArgument_ofHoms_of_presentable
      (fun q => (boundedIntervalGenerator C J s ν q).hom)
      (fun _ => isPresentable_pointedSimplicialPresheaf _)
  let : HasFactorization K.rlp.llp K.rlp := inferInstance
  let a := factorizationData K.rlp.llp K.rlp (toPoint C X)
  have hmem : K ≤ W := boundedIntervalGenerators_le C J s ν
  have hi : W a.i := rlp_llp_le_intervalLocalExtension J K hmem _ a.hi
  have hp : K.rlp (toPoint C a.Z) := by
    rw [← (point_isZero.{max u v} C).isTerminal.hom_ext a.p (toPoint C a.Z)]
    exact a.hp
  have hY : IsStalkwiseInjectiveFibrant C J a.Z := by
    change (stalkwiseTrivialMonomorphisms C J).rlp (toPoint C a.Z)
    rw [← rlp_boundedTrivialGenerators_eq C J hF ν hν hFν hC hPoint]
    exact antitone_rlp (boundedTrivialGenerators_le_boundedIntervalGenerators C J s ν) _ hp
  refine ⟨a.Z, a.i, intervalLocalExtension_le_intervalWeakEquivalences J _ hi, ?_⟩
  exact isIntervalLocal_of_rlp_monomorphisms_exponentialPre J s hY
    (rlp_exponentialPre_of_boundedIntervalGenerators C J s ν hp hC)

end CategoryTheory.PointedSimplicialPresheaf

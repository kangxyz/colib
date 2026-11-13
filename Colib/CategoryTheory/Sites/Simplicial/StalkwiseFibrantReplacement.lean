/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.BoundedTrivialLifting
public import Colib.CategoryTheory.Sites.Simplicial.PointedPresentability
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseTrivialComposition
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseTrivialCoproduct
public import Colib.CategoryTheory.SmallObject.Accessible

/-!
# Stalkwise injective fibrant replacement on a site with enough points

The bounded trivial generators give the same right lifting property as
all actual stalkwise trivial monomorphisms. Attach their cells by the
native small object argument and use the established closure properties
for the original left map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MorphismProperty Opposite SimplicialSubpresheaf

universe v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C) [J.HasEnoughPoints.{max u v}]

/-- The native factorization into a stalkwise trivial monomorphism and a
map lifting against all stalkwise trivial monomorphisms. -/
theorem hasFactorization_stalkwiseTrivialMonomorphisms_rlp :
    HasFactorization (stalkwiseTrivialMonomorphisms.{max u v} C J)
      (stalkwiseTrivialMonomorphisms.{max u v} C J).rlp := by
  constructor
  intro X Y f
  obtain ⟨F, hSmall, hF⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty J
  let : ObjectProperty.Small.{max u v} F := hSmall
  obtain ⟨κ, hReg, hκ, hFκ, hC, hPoint⟩ := exists_regular_cardinal_bounds (F := F)
  let : Fact κ.IsRegular := hReg
  let I := boundedTrivialGenerators C J κ
  let W := stalkwiseTrivialMonomorphisms C J
  have hI : I ≤ W := boundedTrivialGenerators_le C J κ
  have hEq : I.rlp = W.rlp := rlp_boundedTrivialGenerators_eq C J hF κ hκ hFκ hC hPoint
  let : LocallySmall.{max u v} (PointedSimplicialPresheaf.{max u v} C) :=
    CategoryTheory.locallySmall_self _
  have hSOA : HasSmallObjectArgument.{max u v} I :=
    hasSmallObjectArgument_ofHoms_of_presentable
      (fun q : BoundedTrivialArrow C J κ => (free C).map q.val.2.2)
      (fun _ => isPresentable_pointedSimplicialPresheaf _)
  obtain ⟨ν, hν, hbot, hsoa⟩ := hSOA.exists_cardinal
  let : Fact ν.IsRegular := hν
  let : OrderBot ν.ord.ToType := hbot
  let : I.IsCardinalForSmallObjectArgument ν := hsoa
  let i := SmallObject.ιObj I ν f
  let p := SmallObject.πObj I ν f
  have hp : W.rlp p := hEq ▸ SmallObject.rlp_πObj I ν f
  have hP : (coproducts.{max u v} I).pushouts ≤ W := by
    exact (pushouts_le_iff (Q := W)).2 ((coproducts_le_iff (Q := W)).2 hI)
  have hi := SmallObject.transfiniteCompositionsOfShape_ιObj I ν f
  refine ⟨⟨SmallObject.obj I ν f, i, p, ?_, ?_, hp⟩⟩
  · exact SmallObject.ιObj_πObj I ν f
  · exact W.transfiniteCompositionsOfShape_le ν.ord.ToType i
      (transfiniteCompositionsOfShape_monotone ν.ord.ToType hP i hi)

/-- The original map to the point factors through a stalkwise trivial
monomorphism into an object that lifts against all such monomorphisms. -/
theorem exists_stalkwiseInjectiveFibrantReplacement (X : PointedSimplicialPresheaf.{max u v} C) :
    ∃ (Y : PointedSimplicialPresheaf.{max u v} C) (i : X ⟶ Y),
      stalkwiseTrivialMonomorphisms C J i ∧ IsStalkwiseInjectiveFibrant C J Y := by
  let W := stalkwiseTrivialMonomorphisms.{max u v} C J
  let : HasFactorization W W.rlp := hasFactorization_stalkwiseTrivialMonomorphisms_rlp C J
  let a := factorizationData W W.rlp (toPoint C X)
  refine ⟨a.Z, a.i, a.hi, ?_⟩
  change W.rlp (toPoint C a.Z)
  rw [← (point_isZero.{max u v} C).isTerminal.hom_ext a.p (toPoint C a.Z)]
  exact a.hp

end CategoryTheory.PointedSimplicialPresheaf

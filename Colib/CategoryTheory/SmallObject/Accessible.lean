/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.Presentable.Basic

/-!
# The small object argument for a small family of presentable domains

A single regular cardinal bounds the presentability ranks of the
domains of the chosen family. The native small object argument then
uses that same cardinal for its transfinite cell attachment.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u t

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  {ι : Type t} [Small.{w} ι] {A B : ι → C} (f : ∀ i, A i ⟶ B i)

/-- A small family of arrows with presentable domains admits the native
small object argument when the required colimits exist. -/
theorem hasSmallObjectArgument_ofHoms_of_presentable
    (hA : ∀ i, IsPresentable.{w} (A i)) :
    HasSmallObjectArgument.{w} (ofHoms f) := by
  choose ρ hρ hp using fun i => (hA i).exists_cardinal
  obtain ⟨κ, hκ, hbound⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w}
    (fun i => (ρ i).ord.ToType)
  let : Fact κ.IsRegular := ⟨hκ⟩
  let : Nonempty κ.ord.ToType := Ordinal.nonempty_toType_iff.2
    (fun e => hκ.ne_zero (Cardinal.ord_eq_zero.1 e))
  let bot : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  let : OrderBot κ.ord.ToType := bot
  refine ⟨κ, ⟨hκ⟩, bot, { preservesColimit := ?_ }⟩
  intro _ _ _ _ i hi _ hg
  obtain ⟨j⟩ := hi
  let : Fact (ρ j).IsRegular := hρ j
  let : IsCardinalPresentable (A j) (ρ j) := hp j
  have hle : ρ j ≤ κ := le_of_lt (by
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using hbound j)
  let : IsCardinalPresentable (A j) κ := isCardinalPresentable_of_le _ hle
  let hshape : PreservesColimitsOfShape κ.ord.ToType (coyoneda.obj (Opposite.op (A j))) :=
    preservesColimitsOfShape_of_isCardinalPresentable (A j) κ _
  exact hshape.preservesColimit (K := hg.F)

end CategoryTheory.MorphismProperty

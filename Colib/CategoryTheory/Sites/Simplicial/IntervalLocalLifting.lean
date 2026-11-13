/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalExponential
public import Colib.CategoryTheory.Sites.Simplicial.PresheafPushoutProduct
public import Colib.CategoryTheory.Sites.Simplicial.TrivialFibration
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct

/-!
# The lifting test for interval locality

At a chosen interval point the exponential restriction of a stalkwise
fibrant object lifts against the stalkwise trivial monomorphisms. For
an interval-local object it lifts against every monomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MorphismProperty MonoidalCategory Opposite

universe v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]
  {Y : PointedSimplicialPresheaf.{max u v} C}

private theorem mono_globalPoint {I : Cᵒᵖ ⥤ SSet.{max u v}}
    (s : (⊤_ (Cᵒᵖ ⥤ SSet.{max u v})) ⟶ I) : Mono s :=
  mono_of_mono_fac (terminalIsTerminal.hom_ext (s ≫ terminal.from I) (𝟙 _))

/-- Lifting from the freely pointed map into a pointed target gives
the corresponding underlying extension. -/
theorem hasLiftingProperty_underlying_toPoint_of_free
    {A B : Cᵒᵖ ⥤ SSet.{max u v}} (f : A ⟶ B)
    (h : HasLiftingProperty ((free C).map f) (toPoint C Y)) :
    HasLiftingProperty f (terminal.from Y.right) :=
  (freeForgetAdjunction C).hasLiftingProperty_iff f (toPoint C Y) |>.1 h

variable [MonoidalClosed (Cᵒᵖ ⥤ SSet.{max u v})]
  (J : GrothendieckTopology C)
  {I : Cᵒᵖ ⥤ SSet.{max u v}} (s : (⊤_ (Cᵒᵖ ⥤ SSet.{max u v})) ⟶ I)
  (hY : IsStalkwiseInjectiveFibrant C J Y)

include hY in
private theorem lifts_exponentialPre_of_stalkwiseTrivial
    {A B : Cᵒᵖ ⥤ SSet.{max u v}} (f : A ⟶ B) [Mono f]
    (hf : ∀ Φ : J.Point.{max u v}, SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map f)) :
    HasLiftingProperty f (Under.constantPointExponentialPre s Y).right := by
  let : Mono s := mono_globalPoint s
  have h := hasLiftingProperty_underlying_toPoint_of_free (C := C)
    (Arrow.mk f □ Arrow.mk s).hom
    (hY _ (stalkwiseTrivialMonomorphisms_free_pushoutProduct J f s hf))
  have h' : HasLiftingProperty (Arrow.mk s □ Arrow.mk f).hom (terminal.from Y.right) :=
    (HasLiftingProperty.iff_of_arrow_iso_left
      (Arrow.PushoutProduct.braiding (Arrow.mk f) (Arrow.mk s)) _).1 h
  exact (Arrow.PushoutProduct.hasLiftingProperty_mk_isTerminal_iff terminalIsTerminal).1 h'

include hY in
/-- Restricting a stalkwise fibrant exponential at an interval point
has the injective right lifting property. -/
theorem rlp_stalkwiseTrivial_exponentialPre :
    (stalkwiseTrivialMonomorphisms C J).rlp (Under.constantPointExponentialPre s Y) := by
  intro A B f hf
  let : Mono f := hf.1
  let : Mono f.right := Under.mono_right_of_mono f
  exact hasLiftingProperty_of_right C f _
    (lifts_exponentialPre_of_stalkwiseTrivial J s hY f.right hf.2)

include hY in
/-- For an interval-local fibrant target, evaluation at the original
interval point lifts against every pointed monomorphism. -/
theorem rlp_monomorphisms_exponentialPre
    (h : IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj Y)) :
    (monomorphisms (PointedSimplicialPresheaf.{max u v} C)).rlp
      (Under.constantPointExponentialPre s Y) := by
  let : LocallySmall.{max u v} C := CategoryTheory.locallySmall_max
  exact mono_rlp_of_weak_of_stalkwiseTrivial_rlp C J
    ((isIntervalLocal_iff_stalkwiseWeakEquivalences_exponentialPre J hY s).1 h)
    (rlp_stalkwiseTrivial_exponentialPre J s hY)

include hY in
/-- The original lifting tests imply locality when evaluation at the
parameter point lifts against every pointed monomorphism. -/
theorem isIntervalLocal_of_rlp_monomorphisms_exponentialPre
    (h : (monomorphisms (PointedSimplicialPresheaf.{max u v} C)).rlp
      (Under.constantPointExponentialPre s Y)) :
    IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj Y) := by
  let : LocallySmall.{max u v} C := CategoryTheory.locallySmall_max
  exact (isIntervalLocal_iff_stalkwiseWeakEquivalences_exponentialPre J hY s).2
    (stalkwiseWeakEquivalences_of_mono_rlp C J h)

include hY in
/-- Every cartesian pushout-product of the original interval point
with an unpointed monomorphism lifts into a fibrant interval-local target. -/
theorem lifts_intervalPoint_pushoutProduct
    (h : IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj Y))
    {A B : Cᵒᵖ ⥤ SSet.{max u v}} (f : A ⟶ B) [Mono f] :
    HasLiftingProperty (Arrow.mk s □ Arrow.mk f).hom (terminal.from Y.right) := by
  have hl := rlp_monomorphisms_exponentialPre J s hY h ((free C).map f)
    (mono_free_map C f)
  exact (Arrow.PushoutProduct.hasLiftingProperty_mk_isTerminal_iff terminalIsTerminal).2
    ((freeForgetAdjunction C).hasLiftingProperty_iff f _ |>.1 hl)

end CategoryTheory.PointedSimplicialPresheaf

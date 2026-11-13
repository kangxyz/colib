/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalLifting
public import Colib.CategoryTheory.Sites.Simplicial.CylinderHomotopyExtension
import Colib.CategoryTheory.Limits.UnderLifting
import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Extension of pointed maps and cylinder homotopies into local targets

The two right maps test strict extension and extension with the two
original simplicial endpoints prescribed. For pointed maps a lifted
unpointed cylinder retains the prescribed basepoint track.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MorphismProperty MonoidalCategory Opposite

universe v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]
  [MonoidalClosed (Cᵒᵖ ⥤ SSet.{max u v})]
  (J : GrothendieckTopology C)
  {I : Cᵒᵖ ⥤ SSet.{max u v}} (s : (⊤_ (Cᵒᵖ ⥤ SSet.{max u v})) ⟶ I)

private abbrev pathRestriction (E : PointedSimplicialPresheaf.{max u v} C) :=
  (MonoidalClosed.pre (simplicialIntervalBoundary.{max u v} C)).app E.right

private abbrev FibrantLocalTarget :=
  {E : PointedSimplicialPresheaf.{max u v} C // IsStalkwiseInjectiveFibrant C J E ∧
    IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj E)}

omit [MonoidalClosed (Cᵒᵖ ⥤ SSet.{max u v})] in
private theorem terminalRightMap_lifts {A B : Cᵒᵖ ⥤ SSet.{max u v}} {f : A ⟶ B}
    (h : ∀ E : FibrantLocalTarget (I := I) J, HasLiftingProperty f (terminal.from E.val.right)) :
    (MorphismProperty.ofHoms
      (fun E : FibrantLocalTarget (I := I) J => terminal.from E.val.right)).llp f := by
  intro X Y p hp
  obtain ⟨E⟩ := hp
  exact h E

private theorem pathRightMap_lifts {A B : Cᵒᵖ ⥤ SSet.{max u v}} {f : A ⟶ B}
    (h : ∀ E : FibrantLocalTarget (I := I) J, HasLiftingProperty f (pathRestriction E.val)) :
    (MorphismProperty.ofHoms
      (fun E : FibrantLocalTarget (I := I) J => pathRestriction E.val)).llp f := by
  intro X Y p hp
  obtain ⟨E⟩ := hp
  exact h E

private abbrev terminalRightMaps : MorphismProperty (Cᵒᵖ ⥤ SSet.{max u v}) :=
  MorphismProperty.ofHoms (fun E : FibrantLocalTarget (I := I) J => terminal.from E.val.right)

private abbrev pathRightMaps : MorphismProperty (Cᵒᵖ ⥤ SSet.{max u v}) :=
  MorphismProperty.ofHoms (fun E : FibrantLocalTarget (I := I) J => pathRestriction E.val)

private def localRightMaps :
    MorphismProperty (Cᵒᵖ ⥤ SSet.{max u v}) :=
  terminalRightMaps (I := I) J ⊔ pathRightMaps (I := I) J

/-- Underlying left lifting against the actual local extension tests. -/
@[no_expose]
def intervalLocalExtension : MorphismProperty (PointedSimplicialPresheaf.{max u v} C) :=
  ((localRightMaps (I := I) J).inverseImage (forget C)).llp

/-- Left lifting against the right class of any family satisfying the
local extension tests again satisfies those tests. -/
theorem rlp_llp_le_intervalLocalExtension
    (F : MorphismProperty (PointedSimplicialPresheaf.{max u v} C))
    (hF : F ≤ intervalLocalExtension (I := I) J) :
    F.rlp.llp ≤ intervalLocalExtension (I := I) J :=
  antitone_llp ((le_llp_iff_le_rlp F _).1 hF)

private theorem localRightMaps_llp_iff {A B : Cᵒᵖ ⥤ SSet.{max u v}} (f : A ⟶ B) :
    (localRightMaps (I := I) J).llp f ↔
      ∀ E : FibrantLocalTarget (I := I) J, HasLiftingProperty f (terminal.from E.val.right) ∧
        HasLiftingProperty f (pathRestriction E.val) := by
  constructor
  · intro h E
    have h₀ : terminalRightMaps (I := I) J (terminal.from E.val.right) := ⟨E⟩
    have h₁ : pathRightMaps (I := I) J (pathRestriction E.val) := ⟨E⟩
    exact ⟨h _ (Or.inl h₀), h _ (Or.inr h₁)⟩
  · intro h X Y p hp
    change terminalRightMaps (I := I) J p ∨ pathRightMaps (I := I) J p at hp
    rcases hp with h₀ | h₁
    · exact terminalRightMap_lifts J (fun E => (h E).1) p h₀
    · exact pathRightMap_lifts J (fun E => (h E).2) p h₁

private theorem intervalLocalExtension_iff
    {X Y : PointedSimplicialPresheaf.{max u v} C} (f : X ⟶ Y) :
    intervalLocalExtension (I := I) J f ↔
      ∀ (E : PointedSimplicialPresheaf.{max u v} C),
        IsStalkwiseInjectiveFibrant C J E →
        IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj E) →
        HasLiftingProperty f.right (terminal.from E.right) ∧
          HasLiftingProperty (Arrow.mk f.right □
            Arrow.mk (simplicialIntervalBoundary.{max u v} C)).hom
            (terminal.from E.right) := by
  change ((localRightMaps (I := I) J).inverseImage (forget C)).llp f ↔ _
  rw [← Under.inverseImage_llp]
  change (localRightMaps (I := I) J).llp f.right ↔ _
  rw [localRightMaps_llp_iff]
  have he (E : PointedSimplicialPresheaf.{max u v} C) :
      HasLiftingProperty (Arrow.mk f.right □
        Arrow.mk (simplicialIntervalBoundary.{max u v} C)).hom
        (terminal.from E.right) ↔ HasLiftingProperty f.right (pathRestriction E) :=
    ((HasLiftingProperty.iff_of_arrow_iso_left
      (Arrow.PushoutProduct.braiding (Arrow.mk f.right)
        (Arrow.mk (simplicialIntervalBoundary.{max u v} C))) _)).trans
      (Arrow.PushoutProduct.hasLiftingProperty_mk_isTerminal_iff terminalIsTerminal)
  constructor
  · intro h E hE hL
    let E' : FibrantLocalTarget (I := I) J := ⟨E, hE, hL⟩
    exact ⟨(h E').1, (he E).2 (h E').2⟩
  · intro h E
    exact ⟨(h E.val E.property.1 E.property.2).1, (he E.val).1
      (h E.val E.property.1 E.property.2).2⟩

/-- The original stalkwise trivial monomorphisms satisfy both extension tests. -/
theorem stalkwiseTrivialMonomorphisms_le_intervalLocalExtension :
    stalkwiseTrivialMonomorphisms C J ≤ intervalLocalExtension (I := I) J := by
  intro A B f hf
  let : Mono f := hf.1
  let : Mono f.right := Under.mono_right_of_mono f
  let d := simplicialIntervalBoundary.{max u v} C
  let : Mono d := mono_simplicialIntervalBoundary C
  apply (intervalLocalExtension_iff J f).2
  intro E hE hL
  exact ⟨hasLiftingProperty_underlying_toPoint_of_free f.right
      (hE _ (stalkwiseTrivialMonomorphisms_free_map C J f.right hf.2)),
    hasLiftingProperty_underlying_toPoint_of_free (Arrow.mk f.right □ Arrow.mk d).hom
      (hE _ (stalkwiseTrivialMonomorphisms_free_pushoutProduct J f.right d hf.2))⟩

/-- A freely pointed pushout-product of the original interval point
with a monomorphism satisfies both local extension tests. -/
theorem intervalLocalExtension_free_intervalPoint_pushoutProduct
    {A B : Cᵒᵖ ⥤ SSet.{max u v}} (f : A ⟶ B) [Mono f] :
    intervalLocalExtension (I := I) J ((free C).map (Arrow.mk s □ Arrow.mk f).hom) := by
  apply (intervalLocalExtension_iff J _).2
  intro E hE hL
  let g := (Arrow.mk s □ Arrow.mk f).hom
  let d := simplicialIntervalBoundary.{max u v} C
  have hg : HasLiftingProperty g (terminal.from E.right) :=
    lifts_intervalPoint_pushoutProduct J s hE hL f
  have hgd : HasLiftingProperty (Arrow.mk g □ Arrow.mk d).hom (terminal.from E.right) := by
    let : Mono d := mono_simplicialIntervalBoundary C
    let : Mono (Arrow.mk f □ Arrow.mk d).hom := mono_presheafPushoutProduct f d
    exact (HasLiftingProperty.iff_of_arrow_iso_left
      (Arrow.PushoutProduct.associator (Arrow.mk s) (Arrow.mk f) (Arrow.mk d)) _).2
      (lifts_intervalPoint_pushoutProduct J s hE hL (Arrow.mk f □ Arrow.mk d).hom)
  have hs : IsPushout g (freeInclusion C _) (freeInclusion C _)
      ((free C).map g).right := (IsPushout.of_coprod_inl_with_id g (⊤_ _)).flip
  let : HasLiftingProperty g (terminal.from E.right) := hg
  have h : HasLiftingProperty ((free C).map g).right (terminal.from E.right) :=
    hs.flip.hasLiftingProperty _
  have h' : HasLiftingProperty ((free C).map g).right (pathRestriction E) := by
    have ht : HasLiftingProperty (Arrow.mk d □ Arrow.mk g).hom (terminal.from E.right) :=
      (HasLiftingProperty.iff_of_arrow_iso_left
        (Arrow.PushoutProduct.braiding (Arrow.mk g) (Arrow.mk d)) _).1 hgd
    let : HasLiftingProperty g (pathRestriction E) :=
      (Arrow.PushoutProduct.hasLiftingProperty_mk_isTerminal_iff terminalIsTerminal).1 ht
    exact hs.flip.hasLiftingProperty _
  refine ⟨h, ?_⟩
  apply (HasLiftingProperty.iff_of_arrow_iso_left
    (Arrow.PushoutProduct.braiding (Arrow.mk ((free C).map g).right) (Arrow.mk d)) _).2
  exact (Arrow.PushoutProduct.hasLiftingProperty_mk_isTerminal_iff terminalIsTerminal).2 h'

theorem surjective_precomp_of_intervalLocalExtension
    {X Y E : PointedSimplicialPresheaf.{max u v} C} {i : X ⟶ Y}
    (hi : intervalLocalExtension (I := I) J i)
    (hE : IsStalkwiseInjectiveFibrant C J E)
    (hL : IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj E)) :
    Function.Surjective (fun f : Y ⟶ E => i ≫ f) := by
  intro f
  let sq : CommSq f.right i.right (terminal.from E.right) (terminal.from Y.right) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  let : HasLiftingProperty i.right (terminal.from E.right) :=
    ((intervalLocalExtension_iff J i).1 hi E hE hL).1
  let l := sq.lift
  have h : Y.hom ≫ l = E.hom := by
    rw [← Under.w i, Category.assoc, sq.fac_left, Under.w f]
  exact ⟨Under.homMk l h, Under.UnderMorphism.ext sq.fac_left⟩

theorem cylinderHomotopic_of_intervalLocalExtension
    {X Y E : PointedSimplicialPresheaf.{max u v} C} {i : X ⟶ Y}
    (hi : intervalLocalExtension (I := I) J i)
    (hE : IsStalkwiseInjectiveFibrant C J E)
    (hL : IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj E))
    {f g : Y ⟶ E} (hfg : CylinderHomotopic (i ≫ f) (i ≫ g)) :
    CylinderHomotopic f g := by
  exact cylinderHomotopic_of_pushoutProduct_lift
    ((intervalLocalExtension_iff J i).1 hi E hE hL).2 hfg

end CategoryTheory.PointedSimplicialPresheaf

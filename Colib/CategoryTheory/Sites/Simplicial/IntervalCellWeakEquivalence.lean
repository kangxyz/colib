/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalExtension
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseFibrantReplacement

/-!
# Interval equivalences of maps with local extension

Extending both strict maps and actual cylinder homotopies gives
bijectivity into each fibrant local target. Fibrant replacement
transports the same test to every object of the stalkwise localization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] [MonoidalClosed (Cᵒᵖ ⥤ SSet.{max u v})]
  (J : GrothendieckTopology C) {I : Cᵒᵖ ⥤ SSet.{max u v}}

private theorem bijective_cylinderHomotopyPrecomp_of_intervalLocalExtension
    {X Y E : PointedSimplicialPresheaf.{max u v} C} (i : X ⟶ Y)
    (hi : intervalLocalExtension (I := I) J i)
    (hE : IsStalkwiseInjectiveFibrant C J E)
    (hL : IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj E)) :
    Function.Bijective (cylinderHomotopyPrecomp (E := E) i) := by
  have hsurj := surjective_precomp_of_intervalLocalExtension J hi hE hL
  refine ⟨?_, ?_⟩
  · intro f g
    refine _root_.Quotient.inductionOn₂ f g (fun f g eq ↦ ?_)
    change _root_.Quotient.mk _ (i ≫ f) = _root_.Quotient.mk _ (i ≫ g) at eq
    apply _root_.Quotient.sound
    have liftClass : ∀ {f g : X ⟶ E}, Relation.EqvGen CylinderHomotopic f g →
        ∀ (a b : Y ⟶ E), i ≫ a = f → i ≫ b = g → Relation.EqvGen CylinderHomotopic a b := by
      intro f g h
      induction h with
      | rel f g h =>
        intro a b ha hb
        exact .rel _ _ (cylinderHomotopic_of_intervalLocalExtension J hi hE hL
          (ha.symm ▸ hb.symm ▸ h))
      | refl f =>
        intro a b ha hb
        have h : CylinderHomotopic (i ≫ a) (i ≫ b) := by
          rw [ha, hb]
          exact ⟨cylinderProjection X (interval C) ≫ f,
            cylinderSection_projection_assoc _ _ _, cylinderSection_projection_assoc _ _ _⟩
        exact .rel _ _ (cylinderHomotopic_of_intervalLocalExtension J hi hE hL h)
      | symm _ _ _ ih =>
        intro a b ha hb
        exact .symm _ _ (ih b a hb ha)
      | trans _ g _ _ _ ih₁ ih₂ =>
        intro a b ha hb
        obtain ⟨c, hc⟩ := hsurj g
        exact .trans _ _ _ (ih₁ a c ha hc) (ih₂ c b hc hb)
    exact liftClass (_root_.Quotient.exact eq) f g rfl rfl
  · intro f
    refine _root_.Quotient.inductionOn f (fun g ↦ ?_)
    obtain ⟨a, ha⟩ := hsurj g
    exact ⟨_root_.Quotient.mk _ a, congrArg (_root_.Quotient.mk _) ha⟩

private theorem bijective_stalkwise_precomp_of_intervalLocalExtension
    {X Y E : PointedSimplicialPresheaf.{max u v} C} (i : X ⟶ Y)
    (hi : intervalLocalExtension (I := I) J i)
    (hE : IsStalkwiseInjectiveFibrant C J E)
    (hL : IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj E)) :
    Function.Bijective (fun f : (toStalkwiseHomotopyCategory C J).obj Y ⟶
      (toStalkwiseHomotopyCategory C J).obj E => (toStalkwiseHomotopyCategory C J).map i ≫ f) := by
  let : LocallySmall.{max u v} C := CategoryTheory.locallySmall_max
  let Q := toStalkwiseHomotopyCategory.{max u v} C J
  let a := stalkwiseFibrantHomEquiv J hE Y
  let b := stalkwiseFibrantHomEquiv J hE X
  let p := cylinderHomotopyPrecomp (E := E) i
  let q := fun f : Q.obj Y ⟶ Q.obj E => Q.map i ≫ f
  have h : q = b.symm ∘ p ∘ a := by
    funext f
    obtain ⟨f₀, rfl⟩ := surjective_stalkwise_map_of_isStalkwiseInjectiveFibrant J hE Y f
    apply b.injective
    change b (Q.map i ≫ Q.map f₀) = b (b.symm (p (a (Q.map f₀))))
    rw [b.apply_symm_apply, ← Q.map_comp]
    change stalkwiseFibrantHomEquiv J hE X (Q.map (i ≫ f₀)) =
      p (stalkwiseFibrantHomEquiv J hE Y (Q.map f₀))
    rw [stalkwiseFibrantHomEquiv_map, stalkwiseFibrantHomEquiv_map]
    rfl
  change Function.Bijective q
  rw [h]
  exact b.symm.bijective.comp
    ((bijective_cylinderHomotopyPrecomp_of_intervalLocalExtension J i hi hE hL).comp a.bijective)

omit [MonoidalClosed (Cᵒᵖ ⥤ SSet.{max u v})] in
private theorem isIntervalLocal_of_iso {L M : StalkwiseHomotopyCategory.{max u v} C J}
    (e : L ≅ M) (hL : IsIntervalLocal C J I L) : IsIntervalLocal C J I M := by
  intro X
  let Q := toStalkwiseHomotopyCategory.{max u v} C J
  let p := Q.map (cylinderProjection X I)
  let a : (Q.obj X ⟶ L) ≃ (Q.obj X ⟶ M) := e.homToEquiv
  let b : (Q.obj (parameterizedCylinder X I) ⟶ L) ≃
      (Q.obj (parameterizedCylinder X I) ⟶ M) := e.homToEquiv
  let r := fun f : Q.obj X ⟶ L => p ≫ f
  have eq : (fun f : Q.obj X ⟶ M => p ≫ f) = b ∘ r ∘ a.symm := by
    funext f
    change p ≫ f = (p ≫ f ≫ e.inv) ≫ e.hom
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Function.Bijective (fun f : Q.obj X ⟶ M => p ≫ f)
  rw [eq]
  exact b.bijective.comp ((hL X).comp a.symm.bijective)

variable [J.HasEnoughPoints.{max u v}]

/-- Maps satisfying both local extension tests are weak for the original interval localization. -/
theorem intervalLocalExtension_le_intervalWeakEquivalences :
    intervalLocalExtension (I := I) J ≤ intervalWeakEquivalences C J I := by
  intro X Y i hi L hL
  let Q := toStalkwiseHomotopyCategory.{max u v} C J
  obtain ⟨E, j, hj, hE⟩ := exists_stalkwiseInjectiveFibrantReplacement C J (Q.objPreimage L)
  let : IsIso (Q.map j) := isIso_toStalkwiseHomotopyCategory_map C j hj.2
  let e : L ≅ Q.obj E := (Q.objObjPreimageIso L).symm ≪≫ asIso (Q.map j)
  have h := bijective_stalkwise_precomp_of_intervalLocalExtension J i hi hE
    (isIntervalLocal_of_iso J e hL)
  let a : (Q.obj Y ⟶ Q.obj E) ≃ (Q.obj Y ⟶ L) := e.symm.homToEquiv
  let b : (Q.obj X ⟶ Q.obj E) ≃ (Q.obj X ⟶ L) := e.symm.homToEquiv
  let p := fun f : Q.obj Y ⟶ Q.obj E => Q.map i ≫ f
  have eq : (fun f : Q.obj Y ⟶ L => Q.map i ≫ f) = b ∘ p ∘ a.symm := by
    funext f
    change Q.map i ≫ f = (Q.map i ≫ f ≫ e.hom) ≫ e.inv
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change Function.Bijective (fun f : Q.obj Y ⟶ L => Q.map i ≫ f)
  rw [eq]
  exact b.bijective.comp (h.comp a.symm.bijective)

end CategoryTheory.PointedSimplicialPresheaf

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Degreewise sheafification of simplicial presheaves

The covering-sieve limit condition in a functor category is degreewise.
Flipping the variables therefore identifies sheaves of diagrams with
diagrams of ordinary sheaves. The ordinary sheafification adjunction,
applied degreewise, supplies the native left exact sheafification of
simplicial presheaves.
-/

@[expose] public noncomputable section

open CategoryTheory Functor Limits

universe w v u q p

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type p} [Category.{q} D] [HasCoproducts.{q} (Type w)]

/-- The sheaf condition for a presheaf of diagrams is the ordinary sheaf
condition in each diagram degree. -/
theorem isSheaf_iff_flip_obj {P : Cᵒᵖ ⥤ D ⥤ Type w} :
    IsSheaf J P ↔ ∀ d : D, IsSheaf J (P.flip.obj d) := by
  constructor
  · intro h d
    rw [isSheaf_iff_isLimit] at h ⊢
    intro X S hS
    exact ⟨isLimitOfPreserves ((evaluation D (Type w)).obj d) (h S hS).some⟩
  · intro h
    rw [isSheaf_iff_isLimit]
    intro X S hS
    exact ⟨evaluationJointlyReflectsLimits _ fun d ↦
      ((isSheaf_iff_isLimit _ _).1 (h d) S hS).some⟩

private def sheafToDegreewise : Sheaf J (D ⥤ Type w) ⥤ D ⥤ Sheaf J (Type w) where
  obj P := ObjectProperty.lift (IsSheaf J) P.obj.flip ((isSheaf_iff_flip_obj J).1 P.property)
  map f :=
    { app := fun d ↦ ⟨f.hom.flipApp d⟩
      naturality := fun _ _ g ↦ Sheaf.hom_ext ((flipFunctor _ _ _).map f.hom |>.naturality g) }

private def degreewiseToSheaf : (D ⥤ Sheaf J (Type w)) ⥤ Sheaf J (D ⥤ Type w) :=
  ObjectProperty.lift (IsSheaf J)
    ((whiskeringRight D _ _).obj (sheafToPresheaf J (Type w)) ⋙ flipFunctor _ _ _)
    (fun P ↦ (isSheaf_iff_flip_obj J).2 fun d ↦ (P.obj d).property)

private def sheafDegreewiseEquivalence : Sheaf J (D ⥤ Type w) ≌ D ⥤ Sheaf J (Type w) where
  functor := sheafToDegreewise J
  inverse := degreewiseToSheaf J
  unitIso := NatIso.ofComponents (fun P ↦ ObjectProperty.isoMk (IsSheaf J)
    (NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _))))
  counitIso := NatIso.ofComponents (fun P ↦ NatIso.ofComponents (fun d ↦
    ObjectProperty.isoMk (IsSheaf J) (NatIso.ofComponents (fun _ ↦ Iso.refl _))))

/-- Ordinary left exact sheafification supplies left exact sheafification
of presheaves valued in a category of diagrams of types. -/
theorem hasSheafify_functorOfTypes [HasSheafify J (Type w)] : HasSheafify J (D ⥤ Type w) := by
  let e := Functor.flipping (C := Cᵒᵖ) (D := D) (E := Type w)
  let s : Sheaf J (D ⥤ Type w) ≌ D ⥤ Sheaf J (Type w) := sheafDegreewiseEquivalence J
  let adj := (e.toAdjunction.comp ((sheafificationAdjunction J (Type w)).whiskerRight D)).comp
    s.symm.toAdjunction
  let : PreservesFiniteLimits ((whiskeringRight D _ _).obj (presheafToSheaf J (Type w))) :=
    ⟨fun K _ _ ↦ inferInstance⟩
  have comparison : s.functor ⋙ (whiskeringRight D _ _).obj (sheafToPresheaf J (Type w)) ⋙
      e.inverse ≅ sheafToPresheaf J (D ⥤ Type w) :=
    NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦
      NatIso.ofComponents (fun _ ↦ Iso.refl _)))
  exact HasSheafify.mk' J _ (adj.ofNatIsoRight comparison)

/-- Simplicial sheafification is available whenever ordinary type-valued
sheafification is available at the same universe. -/
instance [HasSheafify J (Type w)] : HasSheafify J SSet.{w} :=
  hasSheafify_functorOfTypes (D := SimplexCategoryᵒᵖ) J

end CategoryTheory.Presheaf

attribute [colib_tag "COL-0390"]
  CategoryTheory.Presheaf.hasSheafify_functorOfTypes

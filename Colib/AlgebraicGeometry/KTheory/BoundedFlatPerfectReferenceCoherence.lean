/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectNormalizedPullbackAssociativity

/-!
# Reference coherence of normalized pullback factorizations

This internal ingredient of the Bass composition comparison retains the
original scheme-map equality transports. Adapted from
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/NativeReferenceCoherence.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u v
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectReferenceCoherence

section Small
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

/--
Transport a natural isomorphism to the `AsSmall` functors by whiskering with `AsSmall.down` and
`AsSmall.up`.
-/
def smallIso {F G : C ⥤ D} (e : F ≅ G) :
    (AsSmall.down ⋙ F ⋙ AsSmall.up) ≅ (AsSmall.down ⋙ G ⋙ AsSmall.up) :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight e AsSmall.up)

/-- Transport to small categories preserves composition of the reference isomorphisms. -/
theorem smallIso_trans {F G H : C ⥤ D} (e : F ≅ G) (f : G ≅ H) :
    smallIso (e ≪≫ f) = smallIso e ≪≫ smallIso f := by
  apply Iso.ext
  simp only [smallIso, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_comp, whiskerRight_comp]

/-- Transport to small categories commutes with precomposition. -/
theorem smallIso_precomp (F : C ⥤ D) {G H : D ⥤ E} (e : G ≅ H) :
    isoWhiskerLeft (AsSmall.down ⋙ F ⋙ AsSmall.up) (smallIso e) =
      smallIso (isoWhiskerLeft F e) := by
  apply Iso.ext
  ext X
  rfl

/-- Transport to small categories commutes with postcomposition. -/
theorem smallIso_postcomp {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ E) :
    isoWhiskerRight (smallIso e) (AsSmall.down ⋙ H ⋙ AsSmall.up) =
      smallIso (isoWhiskerRight e H) := by
  apply Iso.ext
  ext X
  rfl

/-- Transport of an equality isomorphism is the isomorphism of the induced equality. -/
theorem smallIso_eqToIso {F G : C ⥤ D} (h : F = G) :
    smallIso (eqToIso h) =
      eqToIso (congrArg (fun K ↦ AsSmall.down ⋙ K ⋙ AsSmall.up) h) := by
  subst G
  rfl

end Small

/-- The anchored three-factor routes agree, retaining actual association transports. -/
theorem anchored_three_routes {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (w : X ⟶ T)
    (el : w = (f ≫ g) ≫ h) (er : w = f ≫ g ≫ h) :
    eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback el) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso (f ≫ g) h ≪≫
        isoWhiskerLeft (boundedAboveFlatPerfectNormalizedPullback h)
          (boundedAboveFlatPerfectNormalizedPullbackCompIso f g) =
    eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback er) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso f (g ≫ h) ≪≫
        isoWhiskerRight (boundedAboveFlatPerfectNormalizedPullbackCompIso g h)
          (boundedAboveFlatPerfectNormalizedPullback f) ≪≫
        Functor.associator (boundedAboveFlatPerfectNormalizedPullback h)
          (boundedAboveFlatPerfectNormalizedPullback g)
          (boundedAboveFlatPerfectNormalizedPullback f) := by
  subst w
  apply Iso.ext
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom]
  have ht := boundedAboveFlatPerfectNormalizedPullbackCompIso_two_routes f g h
  have hh := congrArg (fun η ↦
    eqToHom (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.assoc f g h)) ≫ η) ht
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] using hh.symm

/-- The same canonical three-factor equality with both actual equality transports retained. -/
theorem anchored_factorizations {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (d : X ⟶ Z) (e : Y ⟶ T) (w : X ⟶ T)
    (hd : d = f ≫ g) (he : e = g ≫ h) (hl : w = d ≫ h) (hr : w = f ≫ e) :
    eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback hl) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso d h ≪≫
        isoWhiskerLeft (boundedAboveFlatPerfectNormalizedPullback h)
          (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback hd) ≪≫
            boundedAboveFlatPerfectNormalizedPullbackCompIso f g) =
    eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback hr) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso f e ≪≫
        isoWhiskerRight
          (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback he) ≪≫
            boundedAboveFlatPerfectNormalizedPullbackCompIso g h)
          (boundedAboveFlatPerfectNormalizedPullback f) ≪≫
        Functor.associator (boundedAboveFlatPerfectNormalizedPullback h)
          (boundedAboveFlatPerfectNormalizedPullback g)
          (boundedAboveFlatPerfectNormalizedPullback f) := by
  subst d
  subst e
  simpa only [eqToIso_refl, Iso.refl_trans] using anchored_three_routes f g h w hl hr

/-- The same reference equality at the literally associated original functors. -/
theorem anchored_factorizations_strict {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (d : X ⟶ Z) (e : Y ⟶ T) (w : X ⟶ T)
    (hd : d = f ≫ g) (he : e = g ≫ h) (hl : w = d ≫ h) (hr : w = f ≫ e) :
    eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback hl) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso d h ≪≫
        isoWhiskerLeft (boundedAboveFlatPerfectNormalizedPullback h)
          (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback hd) ≪≫
            boundedAboveFlatPerfectNormalizedPullbackCompIso f g) =
    eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback hr) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso f e ≪≫
        isoWhiskerRight
          (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback he) ≪≫
            boundedAboveFlatPerfectNormalizedPullbackCompIso g h)
          (boundedAboveFlatPerfectNormalizedPullback f) := by
  have hA : Functor.associator (boundedAboveFlatPerfectNormalizedPullback h)
      (boundedAboveFlatPerfectNormalizedPullback g) (boundedAboveFlatPerfectNormalizedPullback f) =
      Iso.refl _ := rfl
  simpa only [hA, Iso.trans_refl] using anchored_factorizations f g h d e w hd he hl hr

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectReferenceCoherence

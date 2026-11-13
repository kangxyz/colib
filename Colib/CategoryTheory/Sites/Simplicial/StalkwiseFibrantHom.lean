/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Localization.Representability
public import Colib.CategoryTheory.Sites.Simplicial.CylinderFibrantHomotopy
import Mathlib.CategoryTheory.Types.Basic

/-!
# Morphisms into pointed fibrant presheaves in the stalkwise localization

For an injective fibrant target, homotopy classes for the original
pointed simplicial cylinder represent morphisms in the existing stalkwise
localization. The comparison sends each strict map to its cylinder class.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  (J : GrothendieckTopology C) {E : PointedSimplicialPresheaf.{w} C}
  (hE : IsStalkwiseInjectiveFibrant C J E)

local notation "W" => stalkwiseWeakEquivalences C J
local notation "Q" => toStalkwiseHomotopyCategory C J

include hE in
private theorem cylinderHomotopyClassesFunctor_inverts :
    (W).op.IsInvertedBy (cylinderHomotopyClassesFunctor E) := by
  intro X Y f hf
  apply (CategoryTheory.isIso_iff_bijective _).2
  exact bijective_cylinderHomotopyPrecomp_of_stalkwiseWeakEquivalence J hE f.unop hf

private def localizedCylinderClasses : (StalkwiseHomotopyCategory.{w} C J)ᵒᵖ ⥤ Type (max u w) :=
  Localization.lift (cylinderHomotopyClassesFunctor E)
    (cylinderHomotopyClassesFunctor_inverts J hE) (Q).op

private def cylinderClassesComparison :
    (Q).op ⋙ localizedCylinderClasses J hE ≅ cylinderHomotopyClassesFunctor E :=
  Localization.fac (cylinderHomotopyClassesFunctor E)
    (cylinderHomotopyClassesFunctor_inverts J hE) (Q).op

private def strictMapComparison (X : PointedSimplicialPresheaf.{w} C) (f : X ⟶ E) :
    (localizedCylinderClasses J hE).obj (op ((Q).obj X)) :=
  (cylinderClassesComparison J hE).inv.app (op X) (_root_.Quotient.mk _ f)

private theorem strictMapComparison_naturality {X Y : PointedSimplicialPresheaf.{w} C}
    (i : X ⟶ Y) (g : Y ⟶ E) :
    strictMapComparison J hE X (i ≫ g) =
      (localizedCylinderClasses J hE).map ((Q).map i).op (strictMapComparison J hE Y g) := by
  let η := (cylinderClassesComparison J hE).inv
  have h := ConcreteCategory.congr_hom (η.naturality i.op) (_root_.Quotient.mk _ g)
  change η.app (op X) ((cylinderHomotopyClassesFunctor E).map i.op (_root_.Quotient.mk _ g)) =
    (localizedCylinderClasses J hE).map ((Q).map i).op (η.app (op Y) (_root_.Quotient.mk _ g)) at h
  rw [cylinderHomotopyClassesFunctor_map_mk] at h
  exact h

private theorem strictMapComparison_surjective (X : PointedSimplicialPresheaf.{w} C) :
    Function.Surjective (strictMapComparison J hE X) := by
  intro t
  let e := (cylinderClassesComparison J hE).app (op X)
  obtain ⟨f, hf⟩ := _root_.Quotient.mk_surjective (e.hom t)
  refine ⟨f, ?_⟩
  change e.inv (_root_.Quotient.mk _ f) = t
  rw [hf]
  exact ConcreteCategory.congr_hom e.hom_inv_id t

private theorem strictMapComparison_eq (X : PointedSimplicialPresheaf.{w} C) {f g : X ⟶ E}
    (h : strictMapComparison J hE X f = strictMapComparison J hE X g) :
    (Q).map f = (Q).map g := by
  let e := (cylinderClassesComparison J hE).app (op X)
  have hf : e.inv (_root_.Quotient.mk _ f) = e.inv (_root_.Quotient.mk _ g) := h
  have hq : _root_.Quotient.mk _ f = _root_.Quotient.mk _ g :=
    ((CategoryTheory.isIso_iff_bijective e.inv).1 inferInstance).1 hf
  exact congrArg (cylinderHomotopyClassToStalkwiseHom J X E) hq

/-- Maps into the image of a fibrant pointed presheaf in the actual
stalkwise localization are its cylinder homotopy classes. -/
@[no_expose]
def stalkwiseFibrantHomEquiv (X : PointedSimplicialPresheaf.{w} C) :
    ((Q).obj X ⟶ (Q).obj E) ≃ CylinderHomotopyClasses X E :=
  (Localization.homEquivOfStrictMaps (Q) (W) (localizedCylinderClasses J hE) E
    (strictMapComparison J hE) (strictMapComparison_naturality J hE)
    (strictMapComparison_surjective J hE) (strictMapComparison_eq J hE) X).trans
      (((cylinderClassesComparison J hE).app (op X)).toEquiv)

/-- The Hom correspondence retains the original strict maps. -/
theorem stalkwiseFibrantHomEquiv_map (X : PointedSimplicialPresheaf.{w} C) (f : X ⟶ E) :
    stalkwiseFibrantHomEquiv J hE X ((Q).map f) = _root_.Quotient.mk _ f := by
  let e := (cylinderClassesComparison J hE).app (op X)
  let e₀ := Localization.homEquivOfStrictMaps (Q) (W) (localizedCylinderClasses J hE) E
    (strictMapComparison J hE) (strictMapComparison_naturality J hE)
    (strictMapComparison_surjective J hE) (strictMapComparison_eq J hE) X
  have hf : e₀ ((Q).map f) = e.inv (_root_.Quotient.mk _ f) :=
    Localization.homEquivOfStrictMaps_map (Q) (W) (localizedCylinderClasses J hE) E
      (strictMapComparison J hE) (strictMapComparison_naturality J hE)
      (strictMapComparison_surjective J hE) (strictMapComparison_eq J hE) X f
  change e.hom (e₀ ((Q).map f)) = _root_.Quotient.mk _ f
  exact (congrArg (fun x ↦ e.hom x) hf).trans (ConcreteCategory.congr_hom e.inv_hom_id _)

include hE in
/-- A morphism to the image of a fibrant object admits an actual strict
representative with its original image in the stalkwise localization. -/
theorem surjective_stalkwise_map_of_isStalkwiseInjectiveFibrant
    (X : PointedSimplicialPresheaf.{w} C) :
    Function.Surjective (fun f : X ⟶ E ↦ (Q).map f) := by
  intro g
  let e := stalkwiseFibrantHomEquiv J hE X
  obtain ⟨f, hf⟩ := _root_.Quotient.mk_surjective (e g)
  exact ⟨f, e.injective ((stalkwiseFibrantHomEquiv_map J hE X f).trans hf)⟩

end CategoryTheory.PointedSimplicialPresheaf

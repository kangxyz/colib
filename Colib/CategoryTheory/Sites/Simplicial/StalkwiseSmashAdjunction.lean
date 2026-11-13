/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseFibrantHom
public import Colib.CategoryTheory.Sites.Simplicial.SmashWeakEquivalence
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Yoneda

/-!
# The smash adjunction in the stalkwise homotopy category

Compute the right adjoint on a fibrant representative with the original
pointed internal Hom. The strict adjunction on cylinder homotopy classes
gives the actual Hom equivalence in the stalkwise localization.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  (J : GrothendieckTopology C)
  (T : PointedSimplicialPresheaf.{w} C)
  {G : PointedSimplicialPresheaf.{w} C ⥤ PointedSimplicialPresheaf.{w} C}
  (adj : Under.smashRightFunctor T ⊣ G)

local notation "Q" => toStalkwiseHomotopyCategory C J
local notation "F" => Under.smashRightFunctor T

variable {L : StalkwiseHomotopyCategory.{w} C J ⥤ StalkwiseHomotopyCategory.{w} C J}
  (α : toStalkwiseHomotopyCategory.{w} C J ⋙ L ≅
    Under.smashRightFunctor T ⋙ toStalkwiseHomotopyCategory C J)
  {E : PointedSimplicialPresheaf.{w} C} (hE : IsStalkwiseInjectiveFibrant C J E)

private def localizedSmashHomEquiv (X : PointedSimplicialPresheaf.{w} C) :
    (L.obj ((Q).obj X) ⟶ (Q).obj E) ≃ ((Q).obj X ⟶ (Q).obj (G.obj E)) :=
  ((α.app X).homFromEquiv.trans (stalkwiseFibrantHomEquiv J hE ((F).obj X))).trans
    ((smashAdjunctionCylinderHomotopyEquiv T adj X E).trans
      (stalkwiseFibrantHomEquiv J
        (isStalkwiseInjectiveFibrant_rightAdjoint_smash C J T adj hE) X).symm)

private theorem localizedSmashHomEquiv_map (X : PointedSimplicialPresheaf.{w} C)
    (f : (F).obj X ⟶ E) :
    localizedSmashHomEquiv J T adj α hE X (α.hom.app X ≫ (Q).map f) =
      (Q).map (adj.homEquiv X E f) := by
  let e := stalkwiseFibrantHomEquiv J hE ((F).obj X)
  let e' := stalkwiseFibrantHomEquiv J
    (isStalkwiseInjectiveFibrant_rightAdjoint_smash C J T adj hE) X
  let h := smashAdjunctionCylinderHomotopyEquiv T adj X E
  change e'.symm (h (e ((α.app X).inv ≫ (α.app X).hom ≫ (Q).map f))) = _
  rw [Iso.inv_hom_id_assoc]
  apply e'.injective
  refine (e'.apply_symm_apply _).trans ?_
  calc
    h (e ((Q).map f)) = h (_root_.Quotient.mk _ f) :=
      congrArg h (stalkwiseFibrantHomEquiv_map J hE ((F).obj X) f)
    _ = _root_.Quotient.mk _ (adj.homEquiv X E f) :=
      smashAdjunctionCylinderHomotopyEquiv_mk T adj f
    _ = e' ((Q).map (adj.homEquiv X E f)) := (stalkwiseFibrantHomEquiv_map J _ X _).symm

private theorem localizedSmashHomEquiv_naturality {X X' : PointedSimplicialPresheaf.{w} C}
    (f : X' ⟶ X) (g : L.obj ((Q).obj X) ⟶ (Q).obj E) :
    localizedSmashHomEquiv J T adj α hE X' (L.map ((Q).map f) ≫ g) =
      (Q).map f ≫ localizedSmashHomEquiv J T adj α hE X g := by
  obtain ⟨g₀, hg₀⟩ := surjective_stalkwise_map_of_isStalkwiseInjectiveFibrant J hE
    ((F).obj X) ((α.app X).inv ≫ g)
  change (Q).map g₀ = (α.app X).inv ≫ g at hg₀
  have hg : g = α.hom.app X ≫ (Q).map g₀ := by
    rw [hg₀]
    exact ((α.app X).hom_inv_id_assoc g).symm
  have h₀ : L.map ((Q).map f) ≫ g =
      α.hom.app X' ≫ (Q).map ((F).map f ≫ g₀) := by
    rw [hg, ← Category.assoc]
    have h := α.hom.naturality f
    change L.map ((Q).map f) ≫ α.hom.app X = α.hom.app X' ≫ (Q).map ((F).map f) at h
    rw [h, Category.assoc, ← (Q).map_comp]
  rw [h₀, hg, localizedSmashHomEquiv_map, localizedSmashHomEquiv_map,
    adj.homEquiv_naturality_left, (Q).map_comp]

/-- The localized Hom equivalence against a fibrant target is natural
in every object of the chosen stalkwise homotopy category. -/
@[no_expose]
def stalkwiseSmashHomNatIso :
    L.op ⋙ CategoryTheory.yoneda.obj ((Q).obj E) ≅
      CategoryTheory.yoneda.obj ((Q).obj (G.obj E)) := by
  let A := L.op ⋙ CategoryTheory.yoneda.obj ((Q).obj E)
  let B := CategoryTheory.yoneda.obj ((Q).obj (G.obj E))
  let e : (Q).op ⋙ A ≅ (Q).op ⋙ B := NatIso.ofComponents
    (fun X ↦ Equiv.toIso (localizedSmashHomEquiv J T adj α hE X.unop))
    (by
      intro X X' f
      ext g
      exact localizedSmashHomEquiv_naturality J T adj α hE f.unop g)
  let H := Localization.fullyFaithfulWhiskeringLeft (Q).op
    (stalkwiseWeakEquivalences.{w} C J).op (Type (max u v (w + 1)))
  exact H.preimageIso e

/-- The represented stalkwise Hom comparison sends an original strict map
to the localization of its strict transpose. -/
theorem stalkwiseSmashHomNatIso_hom_app_map
    (X : PointedSimplicialPresheaf.{w} C) (f : (F).obj X ⟶ E) :
    (stalkwiseSmashHomNatIso J T adj α hE).hom.app (op ((Q).obj X))
      (α.hom.app X ≫ (Q).map f) = (Q).map (adj.homEquiv X E f) := by
  let A := L.op ⋙ CategoryTheory.yoneda.obj ((Q).obj E)
  let B := CategoryTheory.yoneda.obj ((Q).obj (G.obj E))
  let a : (Q).op ⋙ A ≅ (Q).op ⋙ B := NatIso.ofComponents
    (fun X ↦ Equiv.toIso (localizedSmashHomEquiv J T adj α hE X.unop))
    (by
      intro X X' g
      ext z
      exact localizedSmashHomEquiv_naturality J T adj α hE g.unop z)
  let H := Localization.fullyFaithfulWhiskeringLeft (Q).op
    (stalkwiseWeakEquivalences.{w} C J).op (Type (max u v (w + 1)))
  have h : ((Functor.whiskeringLeft _ _ _).obj (Q).op).map
      (stalkwiseSmashHomNatIso J T adj α hE).hom = a.hom := H.map_preimage a.hom
  let g : (A.obj (op ((Q).obj X))) := α.hom.app X ≫ (Q).map f
  have hx : (stalkwiseSmashHomNatIso J T adj α hE).hom.app (op ((Q).obj X)) =
      a.hom.app (op X) := NatTrans.congr_app h (op X)
  have h' := ConcreteCategory.congr_hom hx g
  exact h'.trans (localizedSmashHomEquiv_map J T adj α hE X f)

section Replacement

variable (hrep : ∀ X : PointedSimplicialPresheaf.{w} C,
  ∃ (Y : PointedSimplicialPresheaf.{w} C) (i : X ⟶ Y),
    stalkwiseTrivialMonomorphisms C J i ∧ IsStalkwiseInjectiveFibrant C J Y)

private def fibrantTarget (Y : StalkwiseHomotopyCategory.{w} C J) :=
  (hrep ((Q).objPreimage Y)).choose

omit [LocallySmall.{w} C] in
private theorem fibrantTarget_isFibrant (Y : StalkwiseHomotopyCategory.{w} C J) :
    IsStalkwiseInjectiveFibrant C J (fibrantTarget J hrep Y) :=
  (hrep ((Q).objPreimage Y)).choose_spec.choose_spec.2

private def fibrantTargetIso (Y : StalkwiseHomotopyCategory.{w} C J) :
    Y ≅ (Q).obj (fibrantTarget J hrep Y) := by
  let i := (hrep ((Q).objPreimage Y)).choose_spec.choose
  have hi : stalkwiseWeakEquivalences C J i :=
    (hrep ((Q).objPreimage Y)).choose_spec.choose_spec.1.2
  have hi' : IsIso ((Q).map i) := isIso_toStalkwiseHomotopyCategory_map C i hi
  exact ((Q).objObjPreimageIso Y).symm ≪≫ @asIso _ _ _ _ ((Q).map i) hi'

private def stalkwiseSmashHomEquiv (X Y : StalkwiseHomotopyCategory.{w} C J) :
    (L.obj X ⟶ Y) ≃ (X ⟶ (Q).obj (G.obj (fibrantTarget J hrep Y))) :=
  ((fibrantTargetIso J hrep Y).homToEquiv.trans
    (((stalkwiseSmashHomNatIso J T adj α (fibrantTarget_isFibrant J hrep Y)).app
      (op X)).toEquiv))

include T adj α hrep in
private theorem stalkwiseSmashHomEquiv_naturality
    (X' X Y : StalkwiseHomotopyCategory.{w} C J) (f : X' ⟶ X) (g : L.obj X ⟶ Y) :
    stalkwiseSmashHomEquiv J T adj α hrep X' Y (L.map f ≫ g) =
      f ≫ stalkwiseSmashHomEquiv J T adj α hrep X Y g := by
  let e := fibrantTargetIso J hrep Y
  let h := stalkwiseSmashHomNatIso J T adj α (fibrantTarget_isFibrant J hrep Y)
  let g' : (L.op ⋙ CategoryTheory.yoneda.obj ((Q).obj (fibrantTarget J hrep Y))).obj
      (op X) := g ≫ e.hom
  have hn := ConcreteCategory.congr_hom (h.hom.naturality f.op) g'
  change h.hom.app (op X') (L.map f ≫ g ≫ e.hom) =
    f ≫ h.hom.app (op X) (g ≫ e.hom) at hn
  change h.hom.app (op X') ((L.map f ≫ g) ≫ e.hom) =
    f ≫ h.hom.app (op X) (g ≫ e.hom)
  exact (congrArg (h.hom.app (op X')) (Category.assoc _ _ _)).trans hn

/-- Pointed internal Hom applied to fibrant representatives gives the
right adjoint to the original localized smash. -/
@[no_expose]
def stalkwiseSmashRightAdjoint :
    StalkwiseHomotopyCategory.{w} C J ⥤ StalkwiseHomotopyCategory.{w} C J :=
  Adjunction.rightAdjointOfEquiv (stalkwiseSmashHomEquiv J T adj α hrep)
    (stalkwiseSmashHomEquiv_naturality J T adj α hrep)

/-- The actual smash adjunction in the stalkwise homotopy category. -/
@[no_expose]
def stalkwiseSmashAdjunction : L ⊣ stalkwiseSmashRightAdjoint J T adj α hrep :=
  Adjunction.adjunctionOfEquivRight (stalkwiseSmashHomEquiv J T adj α hrep)
    (stalkwiseSmashHomEquiv_naturality J T adj α hrep)

end Replacement

end CategoryTheory.PointedSimplicialPresheaf

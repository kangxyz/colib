/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.MotivicAdjunction
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.PresheafAdjunction
import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.MotivicBonding
import Colib.CategoryTheory.Sites.Simplicial.StalkwiseFibrantDetection
import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Strict Tate loops on a motivic local fibrant target

The original pointed internal Hom computes Tate loops on a
Nisnevich-injective fibrant, A¹-local target. The comparison carries
the transpose of an original strict map to its motivic transpose.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Cᵣ" => SmoothSite (AlgebraicGeometry.Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (AlgebraicGeometry.Spec R)
local notation "Iᵣ" => affineLineInterval (AlgebraicGeometry.Spec R)
local notation "Qₛ" => toStalkwiseHomotopyCategory Cᵣ Jᵣ
local notation "Qᵢ" => toAffineLineHomotopyCategory (AlgebraicGeometry.Spec R)
local notation "P" => tatePresheafSuspension R
local notation "G" => tatePresheafLoops R
local notation "T" => motivicTateSuspension R
local notation "U" => motivicTateLoops R
local notation "Tₛ" => tateStalkwiseSuspension R

variable (Y : PointedSimplicialPresheaf.{u + 1} (SmoothSite (AlgebraicGeometry.Spec R)))
  (hY : IsStalkwiseInjectiveFibrant (SmoothSite (AlgebraicGeometry.Spec R))
    (SmoothSite.nisnevichTopology (AlgebraicGeometry.Spec R)) Y)
  (hL : IsIntervalLocal (SmoothSite (AlgebraicGeometry.Spec R))
    (SmoothSite.nisnevichTopology (AlgebraicGeometry.Spec R))
    (affineLineInterval (AlgebraicGeometry.Spec R))
    ((toStalkwiseHomotopyCategory (SmoothSite (AlgebraicGeometry.Spec R))
      (SmoothSite.nisnevichTopology (AlgebraicGeometry.Spec R))).obj Y))

private def stalkwiseLoopsHomIso :
    (Tₛ).op ⋙ CategoryTheory.yoneda.obj ((Qₛ).obj Y) ≅
      CategoryTheory.yoneda.obj ((Qₛ).obj ((G).obj Y)) :=
  stalkwiseSmashHomNatIso.{u + 1} Jᵣ (liftedTateSphere R) (tatePresheafAdjunction R)
    (tateStalkwiseSuspensionCompIso R) hY

private def stalkwiseLoopsHomEquiv (X : PointedSimplicialPresheaf.{u + 1} Cᵣ) :
    ((Qₛ).obj ((P).obj X) ⟶ (Qₛ).obj Y) ≃ ((Qₛ).obj X ⟶ (Qₛ).obj ((G).obj Y)) :=
  (((tateStalkwiseSuspensionCompIso R).app X).symm.homFromEquiv).trans
    (((stalkwiseLoopsHomIso R Y hY).app (op ((Qₛ).obj X))).toEquiv)

private theorem stalkwiseLoopsHomEquiv_precomp
    {X X' : PointedSimplicialPresheaf.{u + 1} Cᵣ} (f : X ⟶ X')
    (g : (Qₛ).obj ((P).obj X') ⟶ (Qₛ).obj Y) :
    stalkwiseLoopsHomEquiv R Y hY X ((Qₛ).map ((P).map f) ≫ g) =
      (Qₛ).map f ≫ stalkwiseLoopsHomEquiv R Y hY X' g := by
  let α := tateStalkwiseSuspensionCompIso R
  let a := (stalkwiseLoopsHomIso R Y hY).hom
  let q := (Qₛ).map f
  have hn : (Tₛ).map q ≫ α.hom.app X' = α.hom.app X ≫ (Qₛ).map ((P).map f) :=
    α.hom.naturality f
  let z : (Tₛ).obj ((Qₛ).obj X') ⟶ (Qₛ).obj Y := α.hom.app X' ≫ g
  have ha := ConcreteCategory.congr_hom (a.naturality q.op) z
  change a.app (op ((Qₛ).obj X)) ((Tₛ).map q ≫ α.hom.app X' ≫ g) =
    q ≫ a.app (op ((Qₛ).obj X')) (α.hom.app X' ≫ g) at ha
  change a.app (op ((Qₛ).obj X)) (α.hom.app X ≫ (Qₛ).map ((P).map f) ≫ g) =
    q ≫ a.app (op ((Qₛ).obj X')) (α.hom.app X' ≫ g)
  rwa [← Category.assoc, ← hn, Category.assoc]

private theorem stalkwiseLoopsHomEquiv_map
    (X : PointedSimplicialPresheaf.{u + 1} Cᵣ) (f : (P).obj X ⟶ Y) :
    stalkwiseLoopsHomEquiv R Y hY X ((Qₛ).map f) =
      (Qₛ).map ((tatePresheafAdjunction R).homEquiv X Y f) :=
  stalkwiseSmashHomNatIso_hom_app_map.{u + 1} Jᵣ (liftedTateSphere R) (tatePresheafAdjunction R)
    (tateStalkwiseSuspensionCompIso R) hY X f

include hY hL in
/-- The strict Tate loop of a local fibrant target is A¹-local in Nisnevich homotopy. -/
theorem isIntervalLocal_tatePresheafLoops :
    IsIntervalLocal Cᵣ Jᵣ Iᵣ ((Qₛ).obj ((G).obj Y)) := by
  intro X
  let p := cylinderProjection X Iᵣ
  let b := stalkwiseLoopsHomEquiv R Y hY X
  let c := stalkwiseLoopsHomEquiv R Y hY (parameterizedCylinder X Iᵣ)
  let s := fun f : (Qₛ).obj ((P).obj X) ⟶ (Qₛ).obj Y ↦ (Qₛ).map ((P).map p) ≫ f
  let t := fun f : (Qₛ).obj X ⟶ (Qₛ).obj ((G).obj Y) ↦ (Qₛ).map p ≫ f
  have h : t = c ∘ s ∘ b.symm := by
    funext f
    change (Qₛ).map p ≫ f = c ((Qₛ).map ((P).map p) ≫ b.symm f)
    rw [stalkwiseLoopsHomEquiv_precomp, b.apply_symm_apply]
  change Function.Bijective t
  rw [h]
  have hs : Function.Bijective s :=
    intervalWeakEquivalences_tatePresheafSuspension_map_cylinderProjection R X
      ((Qₛ).obj Y) hL
  exact c.bijective.comp (hs.comp b.symm.bijective)

private def motivicStrictLoopsHomEquiv (X : PointedSimplicialPresheaf.{u + 1} Cᵣ) :
    ((T).obj ((Qᵢ).obj X) ⟶ (Qᵢ).obj Y) ≃ ((Qᵢ).obj X ⟶ (Qᵢ).obj ((G).obj Y)) :=
  (tateSuspensionHomComparison R ((Qᵢ).obj Y) X).trans
    ((intervalLocalHomEquiv Cᵣ Jᵣ Iᵣ Y hL ((P).obj X)).trans
      ((stalkwiseLoopsHomEquiv R Y hY X).trans
        (intervalLocalHomEquiv Cᵣ Jᵣ Iᵣ ((G).obj Y)
          (isIntervalLocal_tatePresheafLoops R Y hY hL) X).symm))

private theorem motivicStrictLoopsHomEquiv_precomp
    {X X' : PointedSimplicialPresheaf.{u + 1} Cᵣ} (f : X ⟶ X')
    (g : (T).obj ((Qᵢ).obj X') ⟶ (Qᵢ).obj Y) :
    motivicStrictLoopsHomEquiv R Y hY hL X ((T).map ((Qᵢ).map f) ≫ g) =
      (Qᵢ).map f ≫ motivicStrictLoopsHomEquiv R Y hY hL X' g := by
  let α := tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)
  let a := intervalLocalHomEquiv Cᵣ Jᵣ Iᵣ ((G).obj Y)
    (isIntervalLocal_tatePresheafLoops R Y hY hL) X
  let a' := intervalLocalHomEquiv Cᵣ Jᵣ Iᵣ ((G).obj Y)
    (isIntervalLocal_tatePresheafLoops R Y hY hL) X'
  let b := intervalLocalHomEquiv Cᵣ Jᵣ Iᵣ Y hL ((P).obj X)
  let b' := intervalLocalHomEquiv Cᵣ Jᵣ Iᵣ Y hL ((P).obj X')
  let c := stalkwiseLoopsHomEquiv R Y hY X
  let c' := stalkwiseLoopsHomEquiv R Y hY X'
  let g' := α.inv.app X' ≫ g
  have hn : (Qᵢ).map ((P).map f) ≫ α.inv.app X' =
      α.inv.app X ≫ (T).map ((Qᵢ).map f) := α.inv.naturality f
  have hp : α.inv.app X ≫ ((T).map ((Qᵢ).map f) ≫ g) =
      (Qᵢ).map ((P).map f) ≫ g' := by
    rw [← Category.assoc, ← hn, Category.assoc]
  have hb : b ((Qᵢ).map ((P).map f) ≫ g') = (Qₛ).map ((P).map f) ≫ b' g' :=
    intervalLocalHomEquiv_naturality Cᵣ Jᵣ Iᵣ Y hL ((P).map f) g'
  have hc : c ((Qₛ).map ((P).map f) ≫ b' g') = (Qₛ).map f ≫ c' (b' g') :=
    stalkwiseLoopsHomEquiv_precomp R Y hY f (b' g')
  have ha : a ((Qᵢ).map f ≫ a'.symm (c' (b' g'))) = (Qₛ).map f ≫ c' (b' g') :=
    (intervalLocalHomEquiv_naturality Cᵣ Jᵣ Iᵣ ((G).obj Y)
      (isIntervalLocal_tatePresheafLoops R Y hY hL) f (a'.symm (c' (b' g')))).trans
        (congrArg ((Qₛ).map f ≫ ·) (a'.apply_symm_apply _))
  change a.symm (c (b (α.inv.app X ≫ ((T).map ((Qᵢ).map f) ≫ g)))) =
    (Qᵢ).map f ≫ a'.symm (c' (b' g'))
  rw [hp, hb, hc, ← ha, a.symm_apply_apply]

private theorem motivicStrictLoopsHomEquiv_map
    (X : PointedSimplicialPresheaf.{u + 1} Cᵣ) (f : (P).obj X ⟶ Y) :
    motivicStrictLoopsHomEquiv R Y hY hL X
      ((tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).hom.app X ≫ (Qᵢ).map f) =
        (Qᵢ).map ((tatePresheafAdjunction R).homEquiv X Y f) := by
  let α := (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).app X
  let a := intervalLocalHomEquiv Cᵣ Jᵣ Iᵣ ((G).obj Y)
    (isIntervalLocal_tatePresheafLoops R Y hY hL) X
  let b := intervalLocalHomEquiv Cᵣ Jᵣ Iᵣ Y hL ((P).obj X)
  let c := stalkwiseLoopsHomEquiv R Y hY X
  let g := (tatePresheafAdjunction R).homEquiv X Y f
  change a.symm (c (b (α.inv ≫ α.hom ≫ (Qᵢ).map f))) = (Qᵢ).map g
  rw [α.inv_hom_id_assoc]
  apply a.injective
  rw [Equiv.apply_symm_apply]
  exact (congrArg c (intervalLocalHomEquiv_map Cᵣ Jᵣ Iᵣ Y hL ((P).obj X) f)).trans
    ((stalkwiseLoopsHomEquiv_map R Y hY X f).trans
      (intervalLocalHomEquiv_map Cᵣ Jᵣ Iᵣ ((G).obj Y)
        (isIntervalLocal_tatePresheafLoops R Y hY hL) X g).symm)

private def motivicStrictLoopsNatIso :
    (T).op ⋙ CategoryTheory.yoneda.obj ((Qᵢ).obj Y) ≅
      CategoryTheory.yoneda.obj ((Qᵢ).obj ((G).obj Y)) := by
  let A := (T).op ⋙ CategoryTheory.yoneda.obj ((Qᵢ).obj Y)
  let B := CategoryTheory.yoneda.obj ((Qᵢ).obj ((G).obj Y))
  let e : (Qᵢ).op ⋙ A ≅ (Qᵢ).op ⋙ B := NatIso.ofComponents
    (fun X ↦ Equiv.toIso (motivicStrictLoopsHomEquiv R Y hY hL X.unop))
    (by
      intro X X' f
      ext g
      exact motivicStrictLoopsHomEquiv_precomp R Y hY hL f.unop g)
  let H := Localization.fullyFaithfulWhiskeringLeft (Qᵢ).op
    (intervalWeakEquivalences Cᵣ Jᵣ Iᵣ).op (Type (u + 2))
  exact H.preimageIso e

private theorem motivicStrictLoopsNatIso_hom_app_map
    (X : PointedSimplicialPresheaf.{u + 1} Cᵣ) (f : (P).obj X ⟶ Y) :
    (motivicStrictLoopsNatIso R Y hY hL).hom.app (op ((Qᵢ).obj X))
      ((tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).hom.app X ≫ (Qᵢ).map f) =
      (Qᵢ).map ((tatePresheafAdjunction R).homEquiv X Y f) := by
  let A := (T).op ⋙ CategoryTheory.yoneda.obj ((Qᵢ).obj Y)
  let B := CategoryTheory.yoneda.obj ((Qᵢ).obj ((G).obj Y))
  let e : (Qᵢ).op ⋙ A ≅ (Qᵢ).op ⋙ B := NatIso.ofComponents
    (fun X ↦ Equiv.toIso (motivicStrictLoopsHomEquiv R Y hY hL X.unop))
    (by
      intro X X' g
      ext z
      exact motivicStrictLoopsHomEquiv_precomp R Y hY hL g.unop z)
  let H := Localization.fullyFaithfulWhiskeringLeft (Qᵢ).op
    (intervalWeakEquivalences Cᵣ Jᵣ Iᵣ).op (Type (u + 2))
  have h : ((Functor.whiskeringLeft _ _ _).obj (Qᵢ).op).map
      (motivicStrictLoopsNatIso R Y hY hL).hom = e.hom := H.map_preimage e.hom
  let g : A.obj (op ((Qᵢ).obj X)) :=
    (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).hom.app X ≫ (Qᵢ).map f
  have hx : (motivicStrictLoopsNatIso R Y hY hL).hom.app (op ((Qᵢ).obj X)) =
      e.hom.app (op X) := NatTrans.congr_app h (op X)
  have h' := ConcreteCategory.congr_hom hx g
  exact h'.trans (motivicStrictLoopsHomEquiv_map R Y hY hL X f)

private def motivicLoopsAdjunctionNatIso :
    (T).op ⋙ CategoryTheory.yoneda.obj ((Qᵢ).obj Y) ≅
      CategoryTheory.yoneda.obj ((U).obj ((Qᵢ).obj Y)) :=
  NatIso.ofComponents
    (fun X ↦ Equiv.toIso ((motivicTateAdjunction R).homEquiv X.unop ((Qᵢ).obj Y)))
    (by
      intro X X' f
      ext g
      exact (motivicTateAdjunction R).homEquiv_naturality_left f.unop g)

/-- The original strict internal Hom computes motivic Tate loops on a local fibrant target. -/
@[no_expose]
def tatePresheafLoopsMotivicIso : (Qᵢ).obj ((G).obj Y) ≅ (U).obj ((Qᵢ).obj Y) :=
  Yoneda.fullyFaithful.preimageIso
    ((motivicStrictLoopsNatIso R Y hY hL).symm ≪≫ motivicLoopsAdjunctionNatIso R Y)

/-- The strict transpose, followed by the actual loop comparison, is
the motivic transpose of the original strict map. -/
theorem tatePresheafLoopsMotivicIso_comp_transpose
    (X : PointedSimplicialPresheaf.{u + 1} Cᵣ) (f : (P).obj X ⟶ Y) :
    (Qᵢ).map ((tatePresheafAdjunction R).homEquiv X Y f) ≫
        (tatePresheafLoopsMotivicIso R Y hY hL).hom =
      (motivicTateAdjunction R).homEquiv ((Qᵢ).obj X) ((Qᵢ).obj Y)
        ((tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).hom.app X ≫ (Qᵢ).map f) := by
  let e := motivicStrictLoopsNatIso R Y hY hL
  let a := motivicLoopsAdjunctionNatIso R Y
  let b := tatePresheafLoopsMotivicIso R Y hY hL
  let g := (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).hom.app X ≫ (Qᵢ).map f
  have he : CategoryTheory.yoneda.map b.hom = (e.symm ≪≫ a).hom :=
    Yoneda.fullyFaithful.map_preimage ((e.symm ≪≫ a).hom)
  let Z := op ((Qᵢ).obj X)
  have hZ : (CategoryTheory.yoneda.map b.hom).app Z = (e.symm ≪≫ a).hom.app Z :=
    NatTrans.congr_app he Z
  have hh := ConcreteCategory.congr_hom hZ (e.hom.app Z g)
  change e.hom.app (op ((Qᵢ).obj X)) g ≫ b.hom =
    a.hom.app (op ((Qᵢ).obj X))
      (e.inv.app (op ((Qᵢ).obj X)) (e.hom.app (op ((Qᵢ).obj X)) g)) at hh
  have hi : e.inv.app (op ((Qᵢ).obj X)) (e.hom.app (op ((Qᵢ).obj X)) g) = g :=
    ((e.app (op ((Qᵢ).obj X))).toEquiv).symm_apply_apply g
  rw [hi, motivicStrictLoopsNatIso_hom_app_map R Y hY hL X f] at hh
  exact hh

/-- An isomorphism in A¹-homotopy between local objects is an
isomorphism in the original stalkwise homotopy category. -/
theorem isIso_stalkwiseMap_of_isIso_motivicMap
    {X Z : PointedSimplicialPresheaf.{u + 1} Cᵣ} (f : X ⟶ Z)
    (hX : IsIntervalLocal Cᵣ Jᵣ Iᵣ ((Qₛ).obj X))
    (hZ : IsIntervalLocal Cᵣ Jᵣ Iᵣ ((Qₛ).obj Z)) (hf : IsIso ((Qᵢ).map f)) :
    IsIso ((Qₛ).map f) := by
  let L := stalkwiseToIntervalHomotopyCategory Cᵣ Jᵣ Iᵣ
  let α := stalkwiseToIntervalHomotopyCategoryCompIso Cᵣ Jᵣ Iᵣ
  let g := (Qₛ).map f
  let a := @asIso _ _ _ _ ((Qᵢ).map f) hf
  let eX := α.app X
  let eZ := α.app Z
  let b := eX ≪≫ a ≪≫ eZ.symm
  have hb : L.map g = b.hom := by
    apply (cancel_mono eZ.hom).1
    have hn : L.map g ≫ eZ.hom = eX.hom ≫ a.hom := α.hom.naturality f
    refine hn.trans ?_
    change eX.hom ≫ a.hom = (eX.hom ≫ a.hom ≫ eZ.inv) ≫ eZ.hom
    calc
      _ = eX.hom ≫ a.hom ≫ eZ.inv ≫ eZ.hom :=
        congrArg (eX.hom ≫ ·)
          (((congrArg (a.hom ≫ ·) eZ.inv_hom_id).trans (Category.comp_id a.hom)).symm)
      _ = _ := by simp only [Category.assoc]
  let : IsIso (L.map g) := hb.symm ▸ b.isIso_hom
  apply isIso_of_yoneda_map_bijective g
  intro W
  let e := stalkwiseIntervalLocalHomEquiv Cᵣ Jᵣ Iᵣ ((Qₛ).obj X) hX W
  let e' := stalkwiseIntervalLocalHomEquiv Cᵣ Jᵣ Iᵣ ((Qₛ).obj Z) hZ W
  let p := fun h : L.obj W ⟶ L.obj ((Qₛ).obj X) ↦ h ≫ L.map g
  have hp : Function.Bijective p :=
    (isIso_iff_yoneda_map_bijective (L.map g)).1 inferInstance (L.obj W)
  have h : (fun h : W ⟶ (Qₛ).obj X ↦ h ≫ g) = e' ∘ p ∘ e.symm := by
    funext h
    apply e'.symm.injective
    change L.map (h ≫ g) = e'.symm (e' (L.map h ≫ L.map g))
    rw [e'.symm_apply_apply]
    exact L.map_comp h g
  rw [h]
  exact e'.bijective.comp (hp.comp e.symm.bijective)

include hY hL in
/-- A strict transpose between local fibrant levels is stalkwise weak when
its motivic transpose is invertible. -/
theorem stalkwiseWeakEquivalences_tateTranspose
    (X : PointedSimplicialPresheaf.{u + 1} Cᵣ)
    (hX : IsStalkwiseInjectiveFibrant Cᵣ Jᵣ X)
    (hXL : IsIntervalLocal Cᵣ Jᵣ Iᵣ ((Qₛ).obj X))
    (f : (P).obj X ⟶ Y)
    (hf : IsIso ((motivicTateAdjunction R).homEquiv ((Qᵢ).obj X) ((Qᵢ).obj Y)
      ((tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).hom.app X ≫ (Qᵢ).map f))) :
    stalkwiseWeakEquivalences Cᵣ Jᵣ ((tatePresheafAdjunction R).homEquiv X Y f) := by
  let g := (tatePresheafAdjunction R).homEquiv X Y f
  let e := tatePresheafLoopsMotivicIso R Y hY hL
  have hh := tatePresheafLoopsMotivicIso_comp_transpose R Y hY hL X f
  have he : IsIso ((Qᵢ).map g ≫ e.hom) := hh.symm ▸ hf
  let : IsIso ((Qᵢ).map g ≫ e.hom) := he
  have hg : IsIso ((Qᵢ).map g) := IsIso.of_isIso_comp_right ((Qᵢ).map g) e.hom
  exact stalkwiseWeakEquivalences_of_isIso_toStalkwiseHomotopyCategory_map g hX
    (isStalkwiseInjectiveFibrant_rightAdjoint_smash Cᵣ Jᵣ (liftedTateSphere R)
      (tatePresheafAdjunction R) hY)
    (isIso_stalkwiseMap_of_isIso_motivicMap R g hXL
      (isIntervalLocal_tatePresheafLoops R Y hY hL) hg)

end AlgebraicGeometry.MotivicHomotopy

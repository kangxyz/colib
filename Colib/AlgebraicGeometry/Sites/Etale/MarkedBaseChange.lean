/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.FrobeniusBaseChangeEquivalence
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Actual marked small étale base change

The marking is the unique lift into the actual fiber product. An equivalence on
small étale sites therefore induces an equivalence of these marked categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.EtaleCohomology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  (f : X ⟶ Y) (ζ : Spec (.of Ω) ⟶ X) (ξ : Spec (.of Ω) ⟶ Y) (h : ζ ≫ f = ξ)

/-- The original functor of scheme-valued lifts, also the native geometric point fiber. -/
abbrev etaleMarkingFiber (X : Scheme.{u}) (ζ : Spec (.of Ω) ⟶ X) : X.Etale ⥤ Type u :=
  Etale.forget X ⋙ coyoneda.obj (op (Over.mk ζ))

/-- Lift the actual marking into the actual small étale base change. -/
def etaleBaseChangeMark (U : Y.Etale) (a : (etaleMarkingFiber Y ξ).obj U) :
    (etaleMarkingFiber X ζ).obj ((smallEtaleBaseChange f).obj U) :=
  Over.homMk (pullback.lift a.left ζ ((Over.w a).trans h.symm)) (by
    change pullback.lift a.left ζ _ ≫ pullback.snd U.hom f = ζ
    simp)

@[reassoc (attr := simp)]
theorem etaleBaseChangeMark_fst (U : Y.Etale) (a : (etaleMarkingFiber Y ξ).obj U) :
    (etaleBaseChangeMark f ζ ξ h U a).left ≫ pullback.fst U.hom f = a.left := by
  apply pullback.lift_fst

@[reassoc]
theorem smallEtaleBaseChange_map_fst {U V : Y.Etale} (g : U ⟶ V) :
    ((smallEtaleBaseChange f).map g).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ g.left := by
  change pullback.map _ _ _ _ g.left (𝟙 X) (𝟙 Y)
    (by simp) (by simp) ≫ _ = _
  simp

@[reassoc]
theorem smallEtaleBaseChange_map_snd {U V : Y.Etale} (g : U ⟶ V) :
    ((smallEtaleBaseChange f).map g).left ≫ pullback.snd V.hom f =
      pullback.snd U.hom f := by
  exact MorphismProperty.Over.w ((smallEtaleBaseChange f).map g)

/-- The actual marked pullback functor, retaining the native site functor and lift. -/
def markedEtaleBaseChange :
    (etaleMarkingFiber Y ξ).Elements ⥤ (etaleMarkingFiber X ζ).Elements where
  obj U := (etaleMarkingFiber X ζ).elementsMk ((smallEtaleBaseChange f).obj U.obj)
    (etaleBaseChangeMark f ζ ξ h U.obj U.val)
  map g := Functor.Elements.homMk ((smallEtaleBaseChange f).map g.hom) (by
    apply Over.OverMorphism.ext
    change (etaleBaseChangeMark f ζ ξ h _ _).left ≫
      ((smallEtaleBaseChange f).map g.hom).left = (etaleBaseChangeMark f ζ ξ h _ _).left
    apply pullback.hom_ext
    · have e := congrArg (fun a ↦ a.left) g.map_val
      change _ ≫ g.hom.left = _ at e
      simpa only [Category.assoc, smallEtaleBaseChange_map_fst,
        etaleBaseChangeMark_fst_assoc, etaleBaseChangeMark_fst] using e
    · simp only [Category.assoc, smallEtaleBaseChange_map_snd]
      exact (Over.w _).trans (Over.w _).symm)
  map_id U := Functor.Elements.hom_ext ((smallEtaleBaseChange f).map_id U.obj)
  map_comp a b := Functor.Elements.hom_ext ((smallEtaleBaseChange f).map_comp a.hom b.hom)

/-- Full faithfulness on the original site descends and detects marked morphisms. -/
def markedEtaleBaseChangeFullyFaithful [(smallEtaleBaseChange f).Full]
    [(smallEtaleBaseChange f).Faithful] : (markedEtaleBaseChange f ζ ξ h).FullyFaithful where
  preimage {U V} g := Functor.Elements.homMk ((smallEtaleBaseChange f).preimage g.hom) (by
    apply Over.OverMorphism.ext
    have e := congrArg (fun a ↦ a.left ≫ pullback.fst V.obj.hom f) g.map_val
    change (etaleBaseChangeMark f ζ ξ h U.obj U.val).left ≫ g.hom.left ≫ _ =
      (etaleBaseChangeMark f ζ ξ h V.obj V.val).left ≫ pullback.fst V.obj.hom f at e
    have e' : (etaleBaseChangeMark f ζ ξ h U.obj U.val).left ≫
        ((smallEtaleBaseChange f).map ((smallEtaleBaseChange f).preimage g.hom)).left ≫
          pullback.fst V.obj.hom f =
        (etaleBaseChangeMark f ζ ξ h V.obj V.val).left ≫ pullback.fst V.obj.hom f := by
      simpa only [Functor.map_preimage] using e
    change U.val.left ≫ ((smallEtaleBaseChange f).preimage g.hom).left = V.val.left
    simpa only [smallEtaleBaseChange_map_fst, etaleBaseChangeMark_fst_assoc,
      etaleBaseChangeMark_fst] using e' )
  map_preimage g := Functor.Elements.hom_ext ((smallEtaleBaseChange f).map_preimage g.hom)
  preimage_map g := Functor.Elements.hom_ext ((smallEtaleBaseChange f).preimage_map g.hom)

/-- A site essential preimage carries the unique marking obtained from the actual projection. -/
theorem markedEtaleBaseChange_essSurj [(smallEtaleBaseChange f).EssSurj] :
    (markedEtaleBaseChange f ζ ξ h).EssSurj := by
  refine ⟨fun V ↦ ?_⟩
  let U := (smallEtaleBaseChange f).objPreimage V.obj
  let e := (smallEtaleBaseChange f).objObjPreimageIso V.obj
  let a : (etaleMarkingFiber Y ξ).obj U := Over.homMk
    (V.val.left ≫ e.inv.left ≫ pullback.fst U.hom f) (by
      change (V.val.left ≫ e.inv.left ≫ pullback.fst U.hom f) ≫ U.hom = ξ
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv.left,
        ]
      have ew : e.inv.left ≫ pullback.snd U.hom f = V.obj.hom :=
        MorphismProperty.Over.w e.inv
      rw [ew, ← Category.assoc]
      have vw : V.val.left ≫ V.obj.hom = ζ := Over.w V.val
      rw [vw, h])
  refine ⟨(etaleMarkingFiber Y ξ).elementsMk U a, ⟨Functor.Elements.isoMk e ?_⟩⟩
  apply Over.OverMorphism.ext
  change (etaleBaseChangeMark f ζ ξ h U a).left ≫ e.hom.left = V.val.left
  have hm : (etaleBaseChangeMark f ζ ξ h U a).left = V.val.left ≫ e.inv.left := by
    apply pullback.hom_ext
    · simp [a]
    · change _ = V.val.left ≫ e.inv.left ≫ ((smallEtaleBaseChange f).obj U).hom
      rw [MorphismProperty.Over.w e.inv]
      exact (Over.w (etaleBaseChangeMark f ζ ξ h U a)).trans (Over.w V.val).symm
  rw [hm, Category.assoc]
  have he := congrArg (fun g ↦ g.left) e.inv_hom_id
  change e.inv.left ≫ e.hom.left = 𝟙 _ at he
  rw [he]
  exact Category.comp_id _

/-- Equivalence on actual small étale objects gives equivalence with the original markings. -/
theorem markedEtaleBaseChange_isEquivalence [(smallEtaleBaseChange f).IsEquivalence] :
    (markedEtaleBaseChange f ζ ξ h).IsEquivalence := by
  let ff := markedEtaleBaseChangeFullyFaithful f ζ ξ h
  exact ⟨ff.faithful, ff.full, markedEtaleBaseChange_essSurj f ζ ξ h⟩

end AlgebraicGeometry.Scheme

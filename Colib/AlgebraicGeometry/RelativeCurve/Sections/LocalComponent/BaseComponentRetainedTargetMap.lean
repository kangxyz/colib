/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BaseComponentRetainedSections
public import Colib.AlgebraicGeometry.Sites.Smooth.Basic

/-! # The actual final retained map and the unchanged original smooth-site targets

The retained source is the literal iterated pullback through the genuine base
change and the chosen component inclusion. Its map to Anew × T is constructed,
not supplied. Retained section factors and the identities with v ≫ f are then
constructed from the original stage section factors and original target maps.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} {A Anew T : SmoothSite S}
  (v : Anew ⟶ A) {X Y V : Scheme.{u}} (q : X ⟶ A.left)
  (j : Y ⟶ X) (κ : V ⟶ pullback q v.left)

/-- The actual two retained pullbacks preserve the original base structure. -/
theorem baseComponentRetained_projection_structure :
    pullback.fst κ (pullback.fst (pullback.fst q v.left) j) ≫ κ ≫
        pullback.snd q v.left ≫ v.left =
      pullback.snd κ (pullback.fst (pullback.fst q v.left) j) ≫
        pullback.snd (pullback.fst q v.left) j ≫ j ≫ q := by
  calc
    _ = pullback.fst κ (pullback.fst (pullback.fst q v.left) j) ≫ κ ≫
        pullback.fst q v.left ≫ q := by
      simpa only [Category.assoc] using congrArg
        (fun t => pullback.fst κ (pullback.fst (pullback.fst q v.left) j) ≫ κ ≫ t)
        (pullback.condition (f := q) (g := v.left)).symm
    _ = pullback.snd κ (pullback.fst (pullback.fst q v.left) j) ≫
        pullback.fst (pullback.fst q v.left) j ≫ pullback.fst q v.left ≫ q := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ pullback.fst q v.left ≫ q)
        (pullback.condition (f := κ) (g := (pullback.fst (pullback.fst q v.left) j)))
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun t => pullback.snd κ (pullback.fst (pullback.fst q v.left) j) ≫ t ≫ q)
        (pullback.condition (f := (pullback.fst q v.left)) (g := j))

variable (r : Y ⟶ pullback A.hom T.hom)
  (hr : r ≫ pullback.fst A.hom T.hom = j ≫ q)

/-- The original retained target map on the actual final retained source. -/
def baseComponentRetainedTargetMap :
    pullback κ (pullback.fst (pullback.fst q v.left) j) ⟶ pullback Anew.hom T.hom :=
  pullback.lift
    (pullback.fst κ (pullback.fst (pullback.fst q v.left) j) ≫ κ ≫ pullback.snd q v.left)
    (pullback.snd κ (pullback.fst (pullback.fst q v.left) j) ≫
      pullback.snd (pullback.fst q v.left) j ≫ r ≫ pullback.snd A.hom T.hom)
    (by
      calc
        _ = (pullback.fst κ (pullback.fst (pullback.fst q v.left) j) ≫ κ ≫
              pullback.snd q v.left ≫ v.left) ≫ A.hom := by
          have hv : v.left ≫ A.hom = Anew.hom := v.w
          simpa only [Category.assoc] using congrArg
            (fun t => pullback.fst κ (pullback.fst (pullback.fst q v.left) j) ≫ κ ≫
              pullback.snd q v.left ≫ t) hv.symm
        _ = (pullback.snd κ (pullback.fst (pullback.fst q v.left) j) ≫
              pullback.snd (pullback.fst q v.left) j ≫ j ≫ q) ≫ A.hom :=
          congrArg (fun t => t ≫ A.hom) (baseComponentRetained_projection_structure v q j κ)
        _ = (pullback.snd κ (pullback.fst (pullback.fst q v.left) j) ≫
              pullback.snd (pullback.fst q v.left) j ≫ r ≫
              pullback.fst A.hom T.hom) ≫ A.hom := by
          simpa only [Category.assoc] using congrArg
            (fun t => pullback.snd κ (pullback.fst (pullback.fst q v.left) j) ≫
              pullback.snd (pullback.fst q v.left) j ≫ t ≫ A.hom) hr.symm
        _ = _ := by
          simpa only [Category.assoc] using congrArg
            (fun t => pullback.snd κ (pullback.fst (pullback.fst q v.left) j) ≫
              pullback.snd (pullback.fst q v.left) j ≫ r ≫ t)
            (pullback.condition (f := A.hom) (g := T.hom)))

@[simp, reassoc] theorem baseComponentRetainedTargetMap_fst :
    baseComponentRetainedTargetMap v q j κ r hr ≫ pullback.fst Anew.hom T.hom =
      pullback.fst κ (pullback.fst (pullback.fst q v.left) j) ≫ κ ≫ pullback.snd q v.left :=
  pullback.lift_fst _ _ _

@[simp, reassoc] theorem baseComponentRetainedTargetMap_snd :
    baseComponentRetainedTargetMap v q j κ r hr ≫ pullback.snd Anew.hom T.hom =
      pullback.snd κ (pullback.fst (pullback.fst q v.left) j) ≫
        pullback.snd (pullback.fst q v.left) j ≫ r ≫ pullback.snd A.hom T.hom :=
  pullback.lift_snd _ _ _

/-- A final retained factor is built from the actual component section, and its
entire target morphism is exactly the original map precomposed by v. -/
theorem exists_baseComponentRetained_section_originalTarget
    (σ : A.left ⟶ X) (hσ : σ ≫ q = 𝟙 A.left)
    (σY : A.left ⟶ Y) (hσY : σY ≫ j = σ)
    (σV : Anew.left ⟶ V) (hσV : σV ≫ κ = baseChangedSection q v.left σ hσ)
    (f : A ⟶ T) (hf : f.left = σY ≫ r ≫ pullback.snd A.hom T.hom) :
    ∃ σRet : Anew.left ⟶ pullback κ (pullback.fst (pullback.fst q v.left) j),
      σRet ≫ pullback.fst κ (pullback.fst (pullback.fst q v.left) j) = σV ∧
      (v ≫ f).left = σRet ≫ baseComponentRetainedTargetMap v q j κ r hr ≫
        pullback.snd Anew.hom T.hom := by
  obtain ⟨σRet, hσRet, hσProj⟩ :=
    exists_baseComponent_retained_section q v.left j σ hσ σY hσY κ σV hσV
  refine ⟨σRet, hσRet, ?_⟩
  have htarget := baseComponent_retained_target q v.left j κ σY
    (r ≫ pullback.snd A.hom T.hom) σRet hσProj
  calc
    (v ≫ f).left = v.left ≫ f.left := rfl
    _ = v.left ≫ σY ≫ r ≫ pullback.snd A.hom T.hom := congrArg (fun t => v.left ≫ t) hf
    _ = σRet ≫ baseComponentRetainedTargetMap v q j κ r hr ≫
        pullback.snd Anew.hom T.hom := by
      simpa only [Category.assoc, baseComponentRetainedTargetMap_snd] using htarget.symm

end AlgebraicGeometry.Scheme.SmoothSite

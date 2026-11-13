/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalization
public import Colib.CategoryTheory.Sites.Simplicial.ReducedCofiberExact
public import Colib.CategoryTheory.Limits.PointedSmash

/-!
# Smash with a pointed parameter as a split cylinder quotient

The pointed cylinder collapses the basepoint axis of the first factor.
Collapsing its section at the parameter point gives the original smash
quotient. The section splits the cylinder projection, so the original
reduced cochains form a split short exact sequence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]
  (X Y : PointedSimplicialPresheaf.{w} C)

private abbrev cylinderInclusion :
    X.right ⨯ Y.right ⟶ (parameterizedCylinder X Y.right).right :=
  pushout.inl (intervalAxis X Y.right) (terminal.from Y.right)

private abbrev parameterAxis : X.right ⟶ X.right ⨯ Y.right :=
  prod.lift (𝟙 X.right) (terminal.from X.right ≫ Y.hom)

/-- The actual quotient map from the pointed cylinder to the smash product. -/
def cylinderToParameterSmash : parameterizedCylinder X Y.right ⟶ Under.smash X Y :=
  Under.homMk (pushout.desc (Under.toSmash X Y) (Under.smash X Y).hom
    (Under.rightAxis_toSmash X Y)) (pushout.inr_desc _ _ _)

/-- The cylinder quotient retains the original map from the product. -/
@[reassoc]
theorem cylinderInclusion_cylinderToParameterSmash :
    pushout.inl (intervalAxis X Y.right) (terminal.from Y.right) ≫
      (cylinderToParameterSmash X Y).right = Under.toSmash X Y :=
  pushout.inl_desc _ _ _

private theorem parameterSection_cylinderToParameterSmash :
    (cylinderSection X Y.hom).right ≫ (cylinderToParameterSmash X Y).right =
      (toPoint C X).right ≫ (fromPoint C (Under.smash X Y)).right :=
  (Category.assoc _ _ _).trans
    ((congrArg (parameterAxis X Y ≫ ·) (cylinderInclusion_cylinderToParameterSmash X Y)).trans
      (Under.leftAxis_toSmash X Y))

/-- Collapsing the actual section at the parameter point gives the
original smash product by its pointed pushout property. -/
theorem cylinderToParameterSmash_isPushout :
    IsPushout (cylinderSection X Y.hom) (toPoint C X)
      (cylinderToParameterSmash X Y) (fromPoint C (Under.smash X Y)) := by
  let F := forget.{w} C
  apply IsPushout.of_map_of_faithful F
  change IsPushout (cylinderSection X Y.hom).right (toPoint C X).right
    (cylinderToParameterSmash X Y).right (fromPoint C (Under.smash X Y)).right
  refine IsPushout.mk' (parameterSection_cylinderToParameterSmash X Y) ?_ ?_
  · intro Z f g hfg hp
    apply pushout.hom_ext
    · exact (cylinderInclusion_cylinderToParameterSmash_assoc X Y f).symm.trans
        ((congrArg (cylinderInclusion X Y ≫ ·) hfg).trans
          (cylinderInclusion_cylinderToParameterSmash_assoc X Y g))
    · exact hp
  · intro Z a b h
    let f := cylinderInclusion X Y ≫ a
    let p := (parameterizedCylinder X Y.right).hom
    have hp : p ≫ a = b := by
      have hi : terminal.from (⊤_ (Cᵒᵖ ⥤ SSet.{w})) = 𝟙 _ := terminal.hom_ext _ _
      have hs := congrArg (X.hom ≫ ·) h
      change X.hom ≫ (cylinderSection X Y.hom).right ≫ a =
        X.hom ≫ terminal.from X.right ≫ b at hs
      rw [← Category.assoc, Under.w, ← Category.assoc, terminal.comp_from, hi,
        Category.id_comp] at hs
      exact hs
    have hAxis₁ : parameterAxis X Y ≫ f = terminal.from X.right ≫ b :=
      (Category.assoc _ _ _).symm.trans h
    have hAxis₂ : intervalAxis X Y.right ≫ f = terminal.from Y.right ≫ b := by
      have hc : intervalAxis X Y.right ≫ cylinderInclusion X Y =
          terminal.from Y.right ≫ p := pushout.condition
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ a) hc).trans ((Category.assoc _ _ _).trans
          (congrArg (terminal.from Y.right ≫ ·) hp)))
    have hd : Under.axesToProduct X Y ≫ f = terminal.from (X.right ⨿ Y.right) ≫ b := by
      apply coprod.hom_ext
      · have h₁ : coprod.inl ≫ Under.axesToProduct X Y = parameterAxis X Y :=
          coprod.inl_desc _ _
        have h₂ : coprod.inl ≫ terminal.from (X.right ⨿ Y.right) = terminal.from X.right :=
          terminal.comp_from _
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ f) h₁).trans (hAxis₁.trans
            ((congrArg (· ≫ b) h₂.symm).trans (Category.assoc _ _ _))))
      · have h₁ : coprod.inr ≫ Under.axesToProduct X Y = intervalAxis X Y.right :=
          coprod.inr_desc _ _
        have h₂ : coprod.inr ≫ terminal.from (X.right ⨿ Y.right) = terminal.from Y.right :=
          terminal.comp_from _
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ f) h₁).trans (hAxis₂.trans
            ((congrArg (· ≫ b) h₂.symm).trans (Category.assoc _ _ _))))
    let g := pushout.desc f b hd
    refine ⟨g, ?_, pushout.inr_desc _ _ _⟩
    apply pushout.hom_ext
    · exact (cylinderInclusion_cylinderToParameterSmash_assoc X Y g).trans
        (pushout.inl_desc _ _ _)
    · change p ≫ ((cylinderToParameterSmash X Y).right ≫ g) = p ≫ a
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ g) (Under.w (cylinderToParameterSmash X Y))).trans
          ((pushout.inr_desc _ _ _).trans hp.symm))

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- The actual section and smash quotient give a short exact sequence
of reduced cochains. The cylinder projection retracts the section. -/
theorem exists_parameterSmashReducedCochains_shortExact :
    let F := reducedCochains.{w} C J
    let i := F.map (cylinderSection X Y.hom)
    let q := F.map (cylinderToParameterSmash X Y)
    ∃ h : i ≫ q = 0, (ShortComplex.mk i q h).ShortExact := by
  let i := cylinderSection X Y.hom
  let p := cylinderProjection X Y.right
  let : Mono i.right := mono_of_mono_fac (congrArg (fun f => f.right)
    (cylinderSection_projection X Y.hom) :
      i.right ≫ p.right = 𝟙 X.right)
  exact exists_reducedCochains_shortExact_of_isPushout_isZero J
    (cylinderToParameterSmash_isPushout X Y) (point_isZero C)

end CategoryTheory.PointedSimplicialPresheaf

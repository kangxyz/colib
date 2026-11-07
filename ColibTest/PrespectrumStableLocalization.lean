/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Colib.Topology.Prespectrum.StableLocalization

/-! Proposed, uncompiled regressions for the original quotient and actual localization.
The universal-property checks use arbitrary independent target universes, evaluate the
lift on original arrows and formal inverse arrows, and check strict uniqueness. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Topology Topology.LoopPrespectrum

universe u v w

namespace PrespectrumStableLocalizationTests

section OriginalMaps

variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F) (g : F ⟶ G)

-- The quotient is Mathlib's quotient of the single native prespectrum category.
example : CoherentHomotopyCategory.{u} =
    CategoryTheory.Quotient coherentHomotopyRelation.{u} := rfl

example : coherentHomotopyRelation f f ↔ Nonempty (Homotopy f f) := Iff.rfl

example {f' : E ⟶ F} (H : Homotopy f f') :
    coherentHomotopyQuotient.map f = coherentHomotopyQuotient.map f' :=
  coherentHomotopyQuotient_map_eq H

example {f' : E ⟶ F} (H : Homotopy f f') :
    toStableLocalization.map f = toStableLocalization.map f' :=
  toStableLocalization_map_eq_of_homotopy H

example : StableLocalization.{u} = coherentStableEquivalences.{u}.Localization := rfl

example : toStableLocalization.map f =
    coherentStableEquivalences.Q.map (coherentHomotopyQuotient.map f) := rfl

example : toStableLocalization.map (𝟙 E) = 𝟙 (toStableLocalization.obj E) :=
  toStableLocalization.map_id E

example : toStableLocalization.map (f ≫ g) =
    toStableLocalization.map f ≫ toStableLocalization.map g :=
  toStableLocalization.map_comp f g

example (d : ℤ) :
    (coherentStableHomotopyFunctor d).map (coherentHomotopyQuotient.map f) =
      (stableHomotopyFunctor d).map f :=
  coherentStableHomotopyFunctor_original_map d f

example (d : ℤ) :
    (localizedStableHomotopyFunctor d).obj (toStableLocalization.obj E) =
      stableHomotopyGroup E d := localizedStableHomotopyFunctor_original_obj d E

example (d : ℤ) :
    (localizedStableHomotopyFunctor d).map (toStableLocalization.map f) =
      (stableHomotopyFunctor d).map f := localizedStableHomotopyFunctor_original_map d f

-- The descended group functors include the actual negative degrees.
example :
    (localizedStableHomotopyFunctor (-1)).map (toStableLocalization.map f) =
      (stableHomotopyFunctor (-1)).map f := localizedStableHomotopyFunctor_original_map (-1) f

example : IsIso (toStableLocalization.map f) ↔ IsStableEquivalence f :=
  toStableLocalization_isIso_iff f

example (hf : IsIso (toStableLocalization.map f)) (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map f) :=
  (toStableLocalization_isIso_iff f).mp hf d

variable (hf : IsStableEquivalence f)

-- The forward arrow is the original arrow, not an unspecified isomorphic replacement.
example : (stableLocalizationIso f hf).hom = toStableLocalization.map f :=
  stableLocalizationIso_hom f hf

example : toStableLocalization.map f ≫ (stableLocalizationIso f hf).inv = 𝟙 _ :=
  (stableLocalizationIso f hf).hom_inv_id

example : (stableLocalizationIso f hf).inv ≫ toStableLocalization.map f = 𝟙 _ :=
  (stableLocalizationIso f hf).inv_hom_id

end OriginalMaps

section UniversalProperty

variable {D : Type v} [Category.{w} D] (T : LoopPrespectrum.{u} ⥤ D)
  (hH : ∀ {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}, Homotopy f g → T.map f = T.map g)
  (hW : ∀ {E F : LoopPrespectrum.{u}} (f : E ⟶ F), IsStableEquivalence f → IsIso (T.map f))

example (E : LoopPrespectrum.{u}) :
    (stableLocalizationHomotopyLift T hH).obj (coherentHomotopyQuotient.obj E) = T.obj E := rfl

example {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    (stableLocalizationHomotopyLift T hH).map (coherentHomotopyQuotient.map f) = T.map f := rfl

-- Inversion on quotient arrows is proved from the original-map assumption.
example : coherentStableEquivalences.IsInvertedBy (stableLocalizationHomotopyLift T hH) :=
  stableLocalizationHomotopyLift_inverts T hH hW

example (E : LoopPrespectrum.{u}) :
    (stableLocalizationLift T hH hW).obj (toStableLocalization.obj E) = T.obj E := rfl

example {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    (stableLocalizationLift T hH hW).map (toStableLocalization.map f) = T.map f := by
  change 𝟙 (T.obj E) ≫ T.map f = T.map f
  exact Category.id_comp _

-- A formal inverse is sent to the actual inverse of the original image in D.
example {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (hf : IsStableEquivalence f) :
    letI : IsIso (T.map f) := hW f hf
    (stableLocalizationLift T hH hW).map (stableLocalizationIso f hf).inv =
      inv (T.map f) := by
  let : IsIso (T.map f) := hW f hf
  change 𝟙 (T.obj F) ≫ inv (T.map f) = inv (T.map f)
  exact Category.id_comp _

example : toStableLocalization ⋙ stableLocalizationLift T hH hW = T :=
  toStableLocalization_comp_lift T hH hW

example (L : StableLocalization.{u} ⥤ D) (hL : toStableLocalization ⋙ L = T) :
    L = stableLocalizationLift T hH hW := stableLocalizationLift_unique T hH hW L hL

example : ∃! L : StableLocalization.{u} ⥤ D, toStableLocalization ⋙ L = T := by
  refine ⟨stableLocalizationLift T hH hW, toStableLocalization_comp_lift T hH hW, ?_⟩
  intro L hL
  exact stableLocalizationLift_unique T hH hW L hL

end UniversalProperty

end PrespectrumStableLocalizationTests

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.StrictDiagramHomotopy
public import Colib.Topology.Prespectrum.HomotopyPushout

/-! # Original coefficient-natural null/unit/null seed word

Only the original whole-word construction and its same-time naturality are selected.
No comparison under Bass, stability or telescope statement is assumed here.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.PushoutStrength
variable {C : Type u} [Category.{v} C]
variable {F₀ F₁ F₂ : C ⥤ LoopPrespectrum.{w}} (f : F₀ ⟶ F₁) (g : F₀ ⟶ F₂)

/-- The actual pointwise reduced homotopy pushout diagram. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/PushoutStrength.lean:30"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
def pushout : C ⥤ LoopPrespectrum.{w} where
  obj X := HomotopyPushout.prespectrum (f.app X) (g.app X)
  map {X Y} k := HomotopyPushout.map (f.app X) (g.app X) (f.app Y) (g.app Y)
    (F₀.map k) (F₁.map k) (F₂.map k) (f.naturality k).symm (g.naturality k).symm
  map_id X := by
    apply HomotopyPushout.hom_ext
    · apply Hom.ext
      funext n
      ext x
      change HomotopyPushout.left (f.app X) (g.app X) n ((F₁.map (𝟙 X)).map n x) =
        HomotopyPushout.left (f.app X) (g.app X) n x
      rw [F₁.map_id]
      rfl
    · apply Hom.ext
      funext n
      ext x
      change HomotopyPushout.right (f.app X) (g.app X) n ((F₂.map (𝟙 X)).map n x) =
        HomotopyPushout.right (f.app X) (g.app X) n x
      rw [F₂.map_id]
      rfl
    · intro n r x
      change HomotopyPushout.cylinder (f.app X) (g.app X) n (r, (F₀.map (𝟙 X)).map n x) =
        HomotopyPushout.cylinder (f.app X) (g.app X) n (r, x)
      rw [F₀.map_id]
      rfl
  map_comp k l := by simp only [Functor.map_comp, HomotopyPushout.map_comp]

end KTheory.Bass.PushoutStrength

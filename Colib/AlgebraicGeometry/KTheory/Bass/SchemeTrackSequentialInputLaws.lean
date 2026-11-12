/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialInput

/-! Whole identity and composition laws for the original finite and suspended input maps. -/
/-!
Implementation provenance: adapted from Quillen at
`SchemeTrackSequentialInputLaws.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeTrackSequentialPresentation

private theorem suspension_id (E : LoopPrespectrum.{w}) :
    suspensionConeMap (𝟙 E) = 𝟙 (suspensionCone E) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext <;> intro z <;> rfl

private theorem suspension_comp {E F G : LoopPrespectrum.{w}} (f : E ⟶ F) (g : F ⟶ G) :
    suspensionConeMap (f ≫ g) = suspensionConeMap f ≫ suspensionConeMap g := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext <;> intro z <;> rfl

/-- The finite original input preserves identities as whole prespectrum maps. -/
theorem input_id (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w}) (X : Scheme.{u}ᵒᵖ) (i : ℕ) :
    input M (𝟙 X) i = 𝟙 _ :=
  ((strictDiagramIterate _ i).obj (M ⋙ prespectrumFunctor)).map_id X

/-- The finite original input preserves compositions as whole prespectrum maps. -/
theorem input_comp (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w}) {X Y Z : Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℕ) :
    input M (f ≫ g) i = input M f i ≫ input M g i :=
  ((strictDiagramIterate _ i).obj (M ⋙ prespectrumFunctor)).map_comp f g

/-- Both original loop and suspension coordinates preserve the identity input. -/
theorem suspendedInput_id
    (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w}) (X : Scheme.{u}ᵒᵖ) (i : ℕ) :
    suspendedInput M (𝟙 X) i = 𝟙 _ := by
  unfold suspendedInput
  rw [input_id, suspension_id]
  exact parameterLoopingFunctor.map_id _

/-- Both original loop and suspension coordinates preserve composite inputs. -/
theorem suspendedInput_comp
    (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w}) {X Y Z : Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℕ) :
    suspendedInput M (f ≫ g) i = suspendedInput M f i ≫ suspendedInput M g i := by
  unfold suspendedInput
  rw [input_comp, suspension_comp]
  exact parameterLoopingFunctor.map_comp _ _

end KTheory.Bass.SchemeTrackSequentialPresentation

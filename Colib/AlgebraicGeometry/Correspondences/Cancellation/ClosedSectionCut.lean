/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor
import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward

/-!
# Principal cut values on closed product supports

If the original support is already a closed subscheme of the source and
target product, the support map of the cut is the zero-fibre inclusion
followed by this original closed immersion. The correspondence value
therefore uses the exact cut cycle on the original support.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme Scheme.AffineLineFiber AlgebraicCycle

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
  (p : P ⟶ X.left) (g : P ⟶ Y.left) (h : p ≫ X.hom = g ≫ Y.hom)

local notation "Z₀(" s ")" => fiber (sectionToAffineLine (p ≫ X.hom) s) 0
local notation "i₀(" s ")" => inclusion (sectionToAffineLine (p ≫ X.hom) s) 0

/-- The cut support map retains both coordinates of the given product map. -/
theorem sectionCutSupportMap_eq_inclusion_comp (m : P ⟶ pullback X.hom Y.hom)
    (hp : m ≫ pullback.fst X.hom Y.hom = p) (hg : m ≫ pullback.snd X.hom Y.hom = g)
    (s : Γ(P, ⊤)) :
    sectionCutSupportMap p g h s = i₀(s) ≫ m := by
  apply pullback.hom_ext
  · rw [sectionCutSupportMap_fst, Category.assoc, hp]
  · rw [sectionCutSupportMap_snd, Category.assoc, hg]

/-- On a closed product support the native correspondence is the successive
pushforward of the whole zero-fibre cycle along both original immersions. -/
theorem sectionCutCorrespondence_val_of_closedSupport [IsNoetherian P]
    (m : P ⟶ pullback X.hom Y.hom) [IsClosedImmersion m]
    (hp : m ≫ pullback.fst X.hom Y.hom = p) (hg : m ≫ pullback.snd X.hom Y.hom = g)
    (s : Γ(P, ⊤)) [IsFinite (i₀(s) ≫ p)]
    (hgen : ∀ z : genericPoints Z₀(s), (i₀(s) ≫ p) z.val ∈ genericPoints X.left) :
    (sectionCutCorrespondence p g h s hgen).val =
      finiteCyclePushforward m (finiteCyclePushforward (i₀(s)) (fundamentalCycle Z₀(s))) := by
  calc
    _ = finiteCyclePushforward (sectionCutSupportMap p g h s) (fundamentalCycle Z₀(s)) :=
      sectionCutCorrespondence_val p g h s hgen
    _ = finiteCyclePushforward (i₀(s) ≫ m) (fundamentalCycle Z₀(s)) :=
      DFunLike.congr_fun (finiteCyclePushforward_congr _ _
        (sectionCutSupportMap_eq_inclusion_comp p g h m hp hg s)) _
    _ = _ := (finiteCyclePushforward_comp_apply (i₀(s)) m (fundamentalCycle Z₀(s))).symm

end AlgebraicGeometry.Cor

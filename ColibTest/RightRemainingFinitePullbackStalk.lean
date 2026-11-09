/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFinitePullbackStalk

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (M : (correspondenceRightIntermediateSupportProduct f g h i z w v).Modules) :
    let ρ := correspondenceRightRemainingFiniteModelProjection f g h i z w v x
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk (ρ q)
    let M' := (Scheme.Modules.pullback ρ).obj M
    letI := stalkModule M' q
    letI := stalkModule M (ρ q)
    letI : Module P (M'.presheaf.stalk q) := Module.compHom _ (ρ.stalkMap q).hom
    (M'.presheaf.stalk q) ≃ₗ[P] (M.presheaf.stalk (ρ q)) := by
  exact correspondenceRightRemainingFinitePullbackStalkLinearEquiv
    f g h i z w v x q M

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (M : (correspondenceRightIntermediateSupportProduct f g h i z w v).Modules)
    {r : ℕ}
    (s : Fin r → (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
      (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q)) :
    let ρ := correspondenceRightRemainingFiniteModelProjection f g h i z w v x
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk (ρ q)
    let M' := (Scheme.Modules.pullback ρ).obj M
    letI := stalkModule M' q
    letI := stalkModule M (ρ q)
    letI : Module P (M'.presheaf.stalk q) := Module.compHom _ (ρ.stalkMap q).hom
    Koszul.seqComplexTensor s (ModuleCat.of P (M'.presheaf.stalk q)) ≅
      Koszul.seqComplexTensor s (ModuleCat.of P (M.presheaf.stalk (ρ q))) := by
  exact correspondenceRightRemainingFinitePullbackKoszulStalkIso
    f g h i z w v x q M s

end Stacks.Chow

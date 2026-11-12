/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionCoefficient

/-! # Generating sections on the actual pullback -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The pulled section generates when its actual zero ideal is the unit
ideal. The invertibility witness is the native pullback of the given module. -/
abbrev sectionGeneratesOnPullback {W X : Scheme.{u}}
    (g : W ⟶ X) (L : X.Modules) [hL : IsInvertibleModule X L] (a : Γ(L, ⊤)) : Prop :=
  @AlgebraicGeometry.zeroScheme W ((Modules.pullback g).obj L)
      (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback W X g L hL)
      (pullbackGlobalSections g L a) = ⊤

/-- The generating condition for the original numerator in the tensor of
the graph line and the specified pole line. -/
abbrev graphNumeratorGeneratesOnPullback {W X : Scheme.{u}} (g : W ⟶ X)
    (D : X.IdealSheafData) [hD : IsEffectiveCartierDivisor D]
    (T : X.Modules) [hT : IsInvertibleModule X T]
    (a : Γ(Stacks.Divisors.tensorModules (divisorSheaf D) T, ⊤)) : Prop :=
  @sectionGeneratesOnPullback W X g (Stacks.Divisors.tensorModules (divisorSheaf D) T)
    (@Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf X (divisorSheaf D) T
      (@Stacks.Divisors.isInvertible_divisorSheaf X D hD) hT) a

/-- The same graph ratio, with the generating condition supplied in its
explicit pullback form. -/
abbrev graphSectionRatioCoefficientOfGenerating {W X : Scheme.{u}} (g : W ⟶ X)
    (D : X.IdealSheafData) [hD : IsEffectiveCartierDivisor D]
    (T : X.Modules) [hT : IsInvertibleModule X T]
    (a : Γ(Stacks.Divisors.tensorModules (divisorSheaf D) T, ⊤)) (b : Γ(T, ⊤))
    (ha : graphNumeratorGeneratesOnPullback g D T a) : Γ(W, ⊤) :=
  @graphSectionRatioCoefficient X W g D hD T hT a b ha

end AlgebraicGeometry.Scheme.RelativeCurvePencil

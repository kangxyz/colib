/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Generators
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularTensorQuotientBoundary

/-!
# The actual ordinary generator ratio is one on the full boundary

The unit is the native ratio of two original ordinary generators. Its boundary value is
computed through actual section pullback, without a generic-field pullback or reduction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.Scheme.Modules

variable {X B : Scheme.{u}} (i : B ⟶ X) (P : X.Modules)
  (U : X.Opens) (hU : (⊤ : B.Opens) ≤ i ⁻¹ᵁ U)
  (p c : Stacks.SheafOfModules.GeneratorSections X.toRingedSpace P U)
  (τ : (pullback i).obj P ≅ SheafOfModules.unit B.ringCatSheaf)

/-- The native unit `c/p`, constructed from the original generators, pulls back to one
when both original ordinary sections have coordinate one in the same boundary frame. -/
@[colib_tag "COL-1063",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/NormInvertible/Generators.lean:224-229,285-293"
    "ingredient" "The actual native ordinary unit comparing the two original generators",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Descent/SectionsPullbackComparison/PullbackSection.lean:76-92"
    "ingredient" "Actual section pullback is semilinear over the original ring map"]
theorem appLE_generatorRatioUnit_eq_one
    (hp : Hom.app τ.hom ⊤ (pullbackSectionHom i P U ⊤ hU p.val) = (1 : Γ(B, ⊤)))
    (hc : Hom.app τ.hom ⊤ (pullbackSectionHom i P U ⊤ hU c.val) = (1 : Γ(B, ⊤))) :
    i.appLE U ⊤ hU (Stacks.SheafOfModules.generatorRatioUnit P U p c).val =
      (1 : Γ(B, ⊤)) := by
  let r : Γ(X, U) := (Stacks.SheafOfModules.generatorRatioUnit P U p c).val
  have hratio : (show Γ(P, U) from c.val) = r • (show Γ(P, U) from p.val) := by
    exact (Stacks.SheafOfModules.generatorRatio_spec P U p c).trans
      (congrArg (fun r : Γ(X, U) => r • (show Γ(P, U) from p.val))
        (Stacks.SheafOfModules.generatorRatioUnit_val P U p c).symm)
  have h := congrArg (fun z => Hom.app τ.hom ⊤ (pullbackSectionHom i P U ⊤ hU z)) hratio
  have hsmul := congrArg (Hom.app τ.hom ⊤)
    (pullbackSectionHom_smul i P U ⊤ hU r (show Γ(P, U) from p.val))
  have hlin := Hom.app_smul τ.hom (i.appLE U ⊤ hU r)
    (pullbackSectionHom i P U ⊤ hU p.val)
  have hcoord := congrArg (fun z : Γ(B, ⊤) => i.appLE U ⊤ hU r • z) hp
  exact (hc.symm.trans (h.trans (hsmul.trans (hlin.trans
    (hcoord.trans (mul_one _)))))).symm

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularGeneratorRatioBoundary
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorQuotient

/-!
# The ordinary generator unit represents the original meromorphic ratio

Only the generic comparison uses integrality. The rational function comes from the actual
unit on the original dense open through the native section-to-rational-function map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsIntegral X] (P : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property P]

local instance regularGeneratorRatioQC : P.IsQuasicoherent :=
  isQuasicoherent_of_isInvertible P

/-- The ordinary ratio unit as a rational unit, using its unchanged dense domain. -/
def rationalGeneratorRatioUnit (U : Stacks.Chow.DenseOpen X)
    (p c : Stacks.SheafOfModules.GeneratorSections X.toRingedSpace P U.val) :
    (Stacks.Chow.rationalFunctions X)ˣ :=
  Units.map (Stacks.Chow.ofSectionRingHom X U).toMonoidHom
    (Stacks.SheafOfModules.generatorRatioUnit P U.val p c)

/-- The literal ordinary generator ratio, with numerator `c` and denominator `p`,
represents the exact native meromorphic ratio of their original generic germs. -/
@[colib_tag "COL-1063",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Chow/RationalFunctions.lean:501-510"
    "ingredient" "The actual ordinary unit maps through the native rational-function ring map",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/Meromorphic/SectionRatio.lean:154-190"
    "ingredient" "Uniqueness identifies the literal native meromorphic ratio"]
theorem rationalGeneratorRatioUnit_eq_meromorphicSectionRatio
    (U : Stacks.Chow.DenseOpen X) (hU : genericPoint X ∈ U.val)
    (p c : Stacks.SheafOfModules.GeneratorSections X.toRingedSpace P U.val)
    (s t : MeromorphicSection X.sheaf P)
    (hs : IsRegularMeromorphicSection X.sheaf P s)
    (ht : IsRegularMeromorphicSection X.sheaf P t)
    (hc : meromorphicGenericValue X P s = P.presheaf.germ U.val (genericPoint X) hU c.val)
    (hp : meromorphicGenericValue X P t = P.presheaf.germ U.val (genericPoint X) hU p.val) :
    rationalGeneratorRatioUnit X P U p c = meromorphicSectionRatio X P s t hs ht := by
  have hratio : IsMeromorphicSectionRatio X P s t (rationalGeneratorRatioUnit X P U p c) := by
    refine ⟨inferInstance, ⟨meromorphicGenericValue X P s, meromorphicGenericValue X P t,
      constantGenericStalkModuleSection_meromorphicGenericValue X P s,
      constantGenericStalkModuleSection_meromorphicGenericValue X P t⟩, ?_⟩
    intro v w hv hw
    have hv' := meromorphicGenericValue_eq X P s v hv
    have hw' := meromorphicGenericValue_eq X P t w hw
    rw [← hv', ← hw', hc, hp]
    let r : Γ(X, U.val) := (Stacks.SheafOfModules.generatorRatioUnit P U.val p c).val
    have hr : (Stacks.Chow.rationalFunctionsEquivFunctionField X).val
        (rationalGeneratorRatioUnit X P U p c).val =
      X.presheaf.germ U.val (genericPoint X) hU r := by
      change (Stacks.Chow.rationalFunctionsEquivFunctionField X).val
        (Stacks.Chow.ofSectionRingHom X U r) = _
      exact (congrArg (Stacks.Chow.rationalFunctionsEquivFunctionField X).val
        (Stacks.Chow.ofSectionRingHom_apply X U r)).trans
          ((Stacks.Chow.rationalFunctionsEquivFunctionField X).property U r hU)
    have hsec : (show Γ(P, U.val) from c.val) = r • (show Γ(P, U.val) from p.val) :=
      (Stacks.SheafOfModules.generatorRatio_spec P U.val p c).trans
        (congrArg (fun z : Γ(X, U.val) => z • (show Γ(P, U.val) from p.val))
          (Stacks.SheafOfModules.generatorRatioUnit_val P U.val p c).symm)
    refine (congrArg (P.presheaf.germ U.val (genericPoint X) hU) hsec).trans ?_
    refine (Scheme.Modules.germ_smul P hU r p.val).trans ?_
    exact congrArg (fun z : X.functionField => z •
      P.presheaf.germ U.val (genericPoint X) hU p.val) hr.symm
  exact (existsUnique_meromorphicSectionRatio X P s t hs ht).unique hratio
    (isMeromorphicSectionRatio_meromorphicSectionRatio X P s t hs ht)

end AlgebraicGeometry

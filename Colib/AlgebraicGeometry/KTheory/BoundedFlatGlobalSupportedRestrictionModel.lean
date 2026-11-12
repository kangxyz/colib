/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedCoefficientRestriction
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedStructure
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportModels
/-! # The original exact supported coefficient restriction

The existing native supported structure and its unchanged chosen zero are reused.
Only the four original restriction results missing from that owner are added here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable (R : CommRingCat.{u}) (c : Index R) {V : Scheme.{u}}
    (k : V ⟶ space c) [IsOpenImmersion k]

/-- Restriction is a categorical equivalence on the actual supported subcategories. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedModels.lean:117"
  "adaptation" "Original exact supported restriction and strict forget square"]
instance supportedRestriction_isEquivalence : (supportedRestriction R c k).IsEquivalence := by
  let : (supportedRestriction R c k ⋙
      boundedAboveFlatCoefficientSupportedEvaluation k).IsEquivalence := by
    rw [supportedRestriction_evaluation]
    exact boundedAboveFlatGlobalSupportedEvaluation_isEquivalence (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k
  exact CategoryTheory.Functor.isEquivalence_of_comp_right
    (supportedRestriction R c k) (boundedAboveFlatCoefficientSupportedEvaluation k)

/-- Supported coefficient restriction is exact by its complete evaluation square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedModels.lean:127"
  "adaptation" "Original exact supported restriction and strict forget square"]
theorem supportedRestriction_exact :
    IsExact (boundedAboveFlatGlobalSupportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k).cof
      (boundedAboveFlatGlobalSupportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k).weq
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen k).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen k).weq
      (supportedRestriction R c k) := by
  have he : IsExact (boundedAboveFlatGlobalSupportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k).cof
      (boundedAboveFlatGlobalSupportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k).weq
      (boundedAboveFlatPerfectSupportedWaldhausen k).cof
      (boundedAboveFlatPerfectSupportedWaldhausen k).weq
      (supportedRestriction R c k ⋙ boundedAboveFlatCoefficientSupportedEvaluation k) := by
    rw [supportedRestriction_evaluation]
    exact boundedAboveFlatGlobalSupportedEvaluation_exact (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k
  exact {
    zero := fun hz => IsZero.of_full_of_faithful_of_isZero
      (boundedAboveFlatCoefficientSupportedEvaluation k) _ (he.zero hz)
    cofibration := fun f hf => he.cofibration f hf
    weak := fun f hf => he.weak f hf
    pushout := fun hi hp => IsPushout.of_map_of_faithful
      (boundedAboveFlatCoefficientSupportedEvaluation k) (he.pushout hi hp) }

/-- The actual supported restriction is a strictly zero-preserving Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedModels.lean:154"
  "adaptation" "Original exact supported restriction and strict forget square"]
def supportedRestrictionModel : boundedAboveFlatGlobalSupportedSectionModel
    (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k ⟶
    boundedAboveFlatCoefficientSupportedSectionModel k :=
  ⟨⟨supportedRestriction R c k, supportedRestriction_exact R c k⟩, by
    apply ObjectProperty.FullSubcategory.ext
    exact ((boundedAboveFlatGlobalCoefficientModelRestriction R).app c).property⟩

/-- Actual supported restriction and forgetting support commute as Model arrows. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedModels.lean:164"
  "adaptation" "Original exact supported restriction and strict forget square"]
theorem supportedRestrictionModel_forget
    {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (a : Under R) :
    supportedRestrictionModel R (Opposite.op Q, a) (schemeMap f a) ≫
        boundedAboveFlatCoefficientSupportedForgetModelMap f a =
      boundedAboveFlatGlobalSupportedForget (X :=
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj
        (Opposite.op Q, a)) (schemeMap f a) ≫
        (boundedAboveFlatGlobalCoefficientModelRestriction R).app (Opposite.op Q, a) := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  exact supportedRestriction_forget R (Opposite.op Q, a) (schemeMap f a)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

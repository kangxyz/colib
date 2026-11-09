/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenLongExactSequence
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenLongExactSequence
public import Colib.KTheory.Waldhausen.Fibration.ConnectingNaturality

/-!
# Forgetting auxiliary support in the relative localization sequence

The actual inclusion preserves both weak structures. Its induced acyclic functor
is the literal union-to-relative-support inclusion after flattening. Consequently
all squares use the original K-maps and original boundary, including K₁ to K₀.
Adapted from Quillen SupportedOpen/Forget.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Waldhausen Fibration
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The same supported inclusion is exact for the two relative coarse structures. -/
theorem perfectSupportedInclusion_open_isExact :
    IsExact (perfectSupportedOpenWeakWaldhausen j T).cof
      (perfectSupportedOpenWeakWaldhausen j T).weq (perfectOpenWeakWaldhausen j).cof
      (perfectOpenWeakWaldhausen j).weq (perfectSupportedInclusion T.ι) where
  zero := (perfectSupportedInclusion_isExact T.ι).zero
  cofibration := (perfectSupportedInclusion_isExact T.ι).cofibration
  weak _ h := h
  pushout := (perfectSupportedInclusion_isExact T.ι).pushout

/-- Forget auxiliary support in the actual relative coarse K-group. -/
def perfectSupportedOpenKForget (n : ℕ) :
    PerfectSupportedOpenCoarseK j T n →* PerfectOpenK j n :=
  KMap (perfectSupportedInclusion_open_isExact j T) n

/-- Forgetting auxiliary support commutes with change of weak equivalences. -/
theorem perfectSupportedOpenKForget_comp_changeWeak (n : ℕ) :
    (perfectSupportedOpenKForget j T n).comp (perfectSupportedOpenKMap j T n) =
      (perfectOpenKMap j n).comp (perfectSupportedKMap T.ι n) := by
  unfold perfectSupportedOpenKForget perfectSupportedOpenKMap perfectOpenKMap perfectSupportedKMap
  erw [KMap_comp_KMap, KMap_comp_KMap]
  rfl

/-- The coarse restriction square uses the original target-support inclusion. -/
theorem perfectSupportedOpenKForget_comp_restrict (n : ℕ) :
    (perfectOpenKRestrict j n).comp (perfectSupportedOpenKForget j T n) =
      (perfectSupportedKMap (j ⁻¹ᵁ T).ι n).comp (perfectSupportedOpenKRestrict j T n) := by
  unfold perfectOpenKRestrict perfectSupportedOpenKForget perfectSupportedKMap
    perfectSupportedOpenKRestrict
  erw [KMap_comp_KMap, KMap_comp_KMap]
  rfl

/-- Forget auxiliary support but retain actual acyclicity on the immersion. -/
def perfectSupportedUnionForget :
    (perfectSupported (T ⊔ j.opensRange).ι).FullSubcategory ⥤
      (perfectSupported j).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K h ↦
    ⟨h.1, ((perfectSupported_sup_opensRange_iff j T K).mp h).2⟩)

/-- The literal union-support inclusion is exact for the inherited fine structures. -/
theorem perfectSupportedUnionForget_isExact :
    IsExact (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof
      (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι).weq
      (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (perfectSupportedUnionForget j T) where
  zero h := by
    apply IsZero.of_full_of_faithful_of_isZero (perfectSupported j).ι
    exact (CofibrationClosedSubcategory.inclusion_exact (complexes X.Modules)
      (perfectSupported (T ⊔ j.opensRange).ι)
      (perfectSupported_cofibrationClosed (T ⊔ j.opensRange).ι)).zero h
  cofibration _ h := h
  weak _ h := h
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (perfectSupported j).ι
    exact CofibrationClosedSubcategory.inclusion_map_pushout (complexes X.Modules)
      (perfectSupported (T ⊔ j.opensRange).ι)
      (perfectSupported_cofibrationClosed (T ⊔ j.opensRange).ι) hi h

/-- The actual union-to-relative-support K-map, in every connective degree. -/
def perfectSupportedUnionForgetKMap (n : ℕ) :
    PerfectSupportedK (T ⊔ j.opensRange).ι n →* PerfectSupportedK j n :=
  KMap (perfectSupportedUnionForget_isExact j T) n

/-- Literal flattening intertwines the actual induced acyclic functor. -/
theorem perfectSupportedOpenAcyclicSupportedKEquiv_forget (n : ℕ) :
    (perfectSupportedUnionForgetKMap j T n).comp
        (perfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (KMap (acyclicFunctor_exact (perfectSupportedOpenNested j T) (perfectOpenNested j)
          (perfectSupportedInclusion_isExact T.ι)
          (perfectSupportedInclusion_open_isExact j T)) n) := by
  change (KMap (perfectSupportedUnionForget_isExact j T) n).comp
    (KMap (perfectSupportedOpenAcyclicToSupported_exact j T) n) =
    (KMap (perfectAcyclicToSupported_exact j) n).comp _
  erw [KMap_comp_KMap, KMap_comp_KMap]
  rfl

/-- Both routes from union support to the base are the same literal inclusion. -/
theorem perfectSupportedUnionKMap_comp_forget (n : ℕ) :
    (perfectSupportedKMap T.ι n).comp (perfectSupportedUnionKMap j T n) =
      (perfectSupportedKMap j n).comp (perfectSupportedUnionForgetKMap j T n) := by
  unfold perfectSupportedKMap perfectSupportedUnionKMap perfectSupportedUnionForgetKMap
  erw [KMap_comp_KMap, KMap_comp_KMap]
  rfl

/-- Forgetting auxiliary support preserves the original relative boundary, also at n = 0. -/
theorem perfectSupportedOpenConnectingHom_forget (n : ℕ) :
    (perfectSupportedUnionForgetKMap j T n).comp (perfectSupportedOpenConnectingHom j T n) =
      (perfectOpenConnectingHom j n).comp (perfectSupportedOpenKForget j T (n + 1)) := by
  unfold perfectSupportedOpenConnectingHom perfectOpenConnectingHom
  erw [← MonoidHom.comp_assoc, perfectSupportedOpenAcyclicSupportedKEquiv_forget,
    MonoidHom.comp_assoc,
    changeWeakConnectingHom_natural (perfectSupportedOpenNested j T) (perfectOpenNested j)
      (perfectSupportedInclusion_isExact T.ι) (perfectSupportedInclusion_open_isExact j T)
      (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T)
      (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n,
    ← MonoidHom.comp_assoc]

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0336",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Forget.lean:30-92"
    "adaptation"
    "Actual coarse and union support inclusions and original connecting-map naturality"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenKForget
  AlgebraicGeometry.Scheme.Modules.perfectSupportedUnionForgetKMap
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenAcyclicSupportedKEquiv_forget
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenConnectingHom_forget

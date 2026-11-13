/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSectionUnits
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportRestriction
public import Colib.CategoryTheory.Functor.IdentityAutomorphismNaturality
public import Colib.RingTheory.Polynomial.LaurentUnderSquare

/-!
# Actual coefficient units on supported native sections

The same forward unit is lifted through the original supported inclusions. Its coefficient
equations and restriction preservation retain the stated original maps.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatPerfectGlobalUnitIso boundedAboveFlatCoefficientSectionLaurentUnitIso

/-- The actual coefficient unit restricted through the original supported section inclusion. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedUnits.lean:36"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportSectionUnitIso {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] (r : (Γ(Spec i.2.right, ⊤))ˣ) :
    𝟭 (BoundedAboveFlatCoefficientSupportedSections j) ≅
      𝟭 (BoundedAboveFlatCoefficientSupportedSections j) :=
  lift (boundedAboveFlatCoefficientSectionSupported j).ι
    (boundedAboveFlatCoefficientSectionUnitIso i (boundedAboveFlatCoefficientUnit i r))

/-- Forgetting support retains exactly the original forward coefficient-unit component. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedUnits.lean:44"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem boundedAboveFlatCoefficientSupportSectionUnitIso_hom {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] (r : (Γ(Spec i.2.right, ⊤))ˣ)
    (S : BoundedAboveFlatCoefficientSupportedSections j) :
    ((boundedAboveFlatCoefficientSupportSectionUnitIso j r).hom.app S).hom =
      (boundedAboveFlatCoefficientSectionUnitIso i (boundedAboveFlatCoefficientUnit i r)).hom.app
        S.obj :=
  map_lift_hom (boundedAboveFlatCoefficientSectionSupported j).ι _ S

/-- Supported reindexing preserves the lifted original identity automorphism. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedUnits.lean:51"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem supportMap_preserves_lift {i k : Index R} {U V : Scheme.{u}}
    (j : U ⟶ space i) (j' : V ⟶ space k) [IsOpenImmersion j] [IsOpenImmersion j']
    (η : i ⟶ k) (l : V ⟶ U) (h : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      η)
    (α : 𝟭 (BoundedAboveFlatCoefficientSections i) ≅ 𝟭 (BoundedAboveFlatCoefficientSections i))
    (β : 𝟭 (BoundedAboveFlatCoefficientSections k) ≅ 𝟭 (BoundedAboveFlatCoefficientSections k))
    (hαβ : Preserves (boundedAboveFlatCoefficientSectionsMap η) α β) :
    Preserves (boundedAboveFlatCoefficientSupportedSectionsMap j j' η l h)
      (lift (boundedAboveFlatCoefficientSectionSupported j).ι α)
      (lift (boundedAboveFlatCoefficientSectionSupported j').ι β) := by
  intro S
  apply ObjectProperty.hom_ext
  change (boundedAboveFlatCoefficientSectionsMap η).map
    ((lift (boundedAboveFlatCoefficientSectionSupported j).ι α).hom.app S).hom =
    ((lift (boundedAboveFlatCoefficientSectionSupported j').ι β).hom.app
      ((boundedAboveFlatCoefficientSupportedSectionsMap j j' η l h).obj S)).hom
  rw [show ((lift (boundedAboveFlatCoefficientSectionSupported j).ι α).hom.app S).hom =
    α.hom.app S.obj from map_lift_hom (boundedAboveFlatCoefficientSectionSupported j).ι α S,
    show ((lift (boundedAboveFlatCoefficientSectionSupported j').ι β).hom.app
      ((boundedAboveFlatCoefficientSupportedSectionsMap j j' η l h).obj S)).hom =
      β.hom.app ((boundedAboveFlatCoefficientSectionsMap η).obj S.obj) from
      map_lift_hom (boundedAboveFlatCoefficientSectionSupported j').ι β _]
  exact hαβ S.obj

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original ambient Laurent unit on its actual auxiliary-supported native fiber. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedUnits.lean:78"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso (Q : Over (Spec R))
    (T : Q.left.Opens) (a : Under R) :=
  lift (boundedAboveFlatCoefficientSectionSupported
    (boundedAboveFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a)).ι).ι
    (boundedAboveFlatCoefficientSectionLaurentUnitIso Q a)

/-- The original restricted Laurent unit on the true open-side auxiliary support. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedUnits.lean:85"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
def boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso (a : Under R) :=
  lift (boundedAboveFlatCoefficientSectionSupported
    (boundedAboveFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj a)).ι).ι
    (boundedAboveFlatCoefficientSectionLaurentUnitIso P a)

omit [IsOpenImmersion f.left] in
/-- Actual ambient supported coefficient reindexing preserves the original Laurent coordinate. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedUnits.lean:92"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso_coefficient
    (Q : Over (Spec R)) (T : Q.left.Opens) {a b : Under R} (g : a ⟶ b) :
    Preserves (boundedAboveFlatCoefficientSupportedAmbientMap T ((laurentUnderFunctor R).map g))
      (boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso Q T a)
      (boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso Q T b) :=
  supportMap_preserves_lift
    (boundedAboveFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a)).ι
    (boundedAboveFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj b)).ι
    (𝟙 (op Q), (laurentUnderFunctor R).map g)
    (boundedAboveFlatCoefficientSupportPairMap Q T ((laurentUnderFunctor R).map g)).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T ((laurentUnderFunctor
      R).map g)))
    _ _ (boundedAboveFlatCoefficientSectionLaurentUnitIso_coefficient Q g)

omit [IsOpenImmersion f.left] in
/-- Actual open-side supported coefficient reindexing preserves the same Laurent coordinate. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedUnits.lean:107"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso_coefficient
    {a b : Under R} (g : a ⟶ b) :
    Preserves (boundedAboveFlatCoefficientSupportedOpenMap f T ((laurentUnderFunctor R).map g))
      (boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso f T a)
      (boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso f T b) :=
  supportMap_preserves_lift
    (boundedAboveFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj a)).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj b)).ι
    (𝟙 (op P), (laurentUnderFunctor R).map g)
    (boundedAboveFlatCoefficientOpenSupportPairMap f T ((laurentUnderFunctor R).map g)).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenSupportPairMap f T
      ((laurentUnderFunctor R).map g)))
    _ _ (boundedAboveFlatCoefficientSectionLaurentUnitIso_coefficient P g)

omit [IsOpenImmersion f.left] in
/-- The actual supported restriction preserves each forward Laurent-unit component. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedUnits.lean:122"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_laurentUnit_preserves (a : Under R) :
    Preserves (boundedAboveFlatCoefficientSupportedOpenRestriction f T
      ((laurentUnderFunctor R).obj a))
      (boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso Q T a)
      (boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso f T a) :=
  supportMap_preserves_lift
    (boundedAboveFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a)).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj a)).ι
    (f.op, 𝟙 ((laurentUnderFunctor R).obj a))
    (supportRestrictionPair (schemeMap f ((laurentUnderFunctor R).obj a))
      (boundedAboveFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a))).left
    (MorphismProperty.Arrow.w (supportRestrictionPair (schemeMap f ((laurentUnderFunctor R).obj a))
      (boundedAboveFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a))))
    _ _ (boundedAboveFlatCoefficientSectionLaurentUnitIso_restriction f a)

omit [IsOpenImmersion f.left] in
/-- Supported restriction retains every original coefficient scalar through its actual map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedUnits.lean:139"
  "adaptation" "Original auxiliary support, Laurent action and selected-null time seed square"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_coefficientUnit_preserves
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedAboveFlatCoefficientSupportedOpenRestriction f T a)
      (boundedAboveFlatCoefficientSupportSectionUnitIso (boundedAboveFlatCoefficientSupportOpen Q
        T a).ι r)
      (boundedAboveFlatCoefficientSupportSectionUnitIso
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι r) :=
  supportMap_preserves_lift (boundedAboveFlatCoefficientSupportOpen Q T a).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι (f.op, 𝟙 a)
    (supportRestrictionPair (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a)).left
    (MorphismProperty.Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a)))
    _ _ (boundedAboveFlatCoefficientSectionsRestriction_unit_preserves f a r)

end AlgebraicGeometry.Scheme.Modules

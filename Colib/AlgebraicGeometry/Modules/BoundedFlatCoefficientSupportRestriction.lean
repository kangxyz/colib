/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportedSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientOpenRestriction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenSupport
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Support

/-!
# Actual auxiliary support and joint coefficient restriction

The specified support opens, inverse-image pair maps, supported section restrictions and literal
coefficient square are preserved. The fiber support is precisely the intersection of the original
auxiliary closed support and localization complement.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatCoefficientSupportedEvaluation
    boundedAboveFlatCoefficientSupportedSectionEquivalence

/-- The auxiliary open on a native fiber is its actual original projection preimage. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:40"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportOpen (Q : Over (Spec R)) (T : Q.left.Opens) (a : Under R) :
    (space (op Q, a)).Opens := projection (op Q, a) ⁻¹ᵁ T

/-- Arbitrary coefficient change retains the exact original support preimage. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:44"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportOpen_preimage
    (Q : Over (Spec R)) (T : Q.left.Opens) {a b : Under R} (g : a ⟶ b) :
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
        (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g) ⁻¹ᵁ
          boundedAboveFlatCoefficientSupportOpen Q T a = boundedAboveFlatCoefficientSupportOpen Q
            T b := by
  change (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g) ≫ projection (op Q, a)) ⁻¹ᵁ T = _
  rw [map_projection]
  rfl

/-- The auxiliary support complement stays quasi-compact under native coefficient base change. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:55"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportOpen_compactSpace
    (Q : Over (Spec R)) (T : Q.left.Opens) [CompactSpace T] (a : Under R) :
    CompactSpace (boundedAboveFlatCoefficientSupportOpen Q T a) := by
  apply isCompact_iff_compactSpace.mp
  have hT : IsCompact (T : Set Q.left) :=
    isCompact_iff_compactSpace.mpr (show CompactSpace T from inferInstance)
  exact (projection (op Q, a)).isCompact_preimage hT

/-- The actual coefficient square between the native auxiliary support opens. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:64"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportPairMap
    (Q : Over (Spec R)) (T : Q.left.Opens) {a b : Under R} (g : a ⟶ b) :
    supportOpenPair (boundedAboveFlatCoefficientSupportOpen Q T b) ⟶
      supportOpenPair (boundedAboveFlatCoefficientSupportOpen Q T a) :=
  let m := AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
  let h := (boundedAboveFlatCoefficientSupportOpen_preimage Q T g).symm.le
  MorphismProperty.Arrow.homMk
    (m.resLE (boundedAboveFlatCoefficientSupportOpen Q T a)
      (boundedAboveFlatCoefficientSupportOpen Q T b) h) m (m.resLE_comp_ι h)

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The open-side auxiliary support complement is the literal native inverse image. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:78"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientOpenSupportOpen (a : Under R) : (space (op P, a)).Opens :=
  schemeMap f a ⁻¹ᵁ boundedAboveFlatCoefficientSupportOpen Q T a

omit [IsOpenImmersion f.left] in
/-- The native open support is the projection preimage of the original open support. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:83"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientOpenSupportOpen_eq (a : Under R) :
    boundedAboveFlatCoefficientOpenSupportOpen f T a =
      projection (op P, a) ⁻¹ᵁ (f.left ⁻¹ᵁ T) := by
  change (schemeMap f a ≫ projection (op Q, a)) ⁻¹ᵁ T = _
  rw [schemeMap_projection]
  rfl

/-- The actual coefficient square on the open-side intersection with auxiliary support. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:91"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientOpenSupportPairMap {a b : Under R} (g : a ⟶ b) :
    supportOpenPair (boundedAboveFlatCoefficientOpenSupportOpen f T b) ⟶
      supportOpenPair (boundedAboveFlatCoefficientOpenSupportOpen f T a) :=
  supportedPairTargetSquare (schemeMap f b) (schemeMap f a)
    (boundedAboveFlatCoefficientSupportPairMap Q T g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedAboveFlatCoefficientOpenSquare f g).symm

/-- Native relative support on the ambient fiber is the original intersection with the closed
complement of the localization open. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:102"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientFiberSupportOpen (a : Under R) : (space (op Q, a)).Opens :=
  boundedAboveFlatCoefficientSupportOpen Q T a ⊔ (schemeMap f a).opensRange

/-- Every native coefficient map preserves this actual intersection support. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:106"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientFiberSupportPairMap {a b : Under R} (g : a ⟶ b) :
    supportOpenPair (boundedAboveFlatCoefficientFiberSupportOpen f T b) ⟶
      supportOpenPair (boundedAboveFlatCoefficientFiberSupportOpen f T a) :=
  supportedPairUnionSquare (schemeMap f b) (schemeMap f a)
    (boundedAboveFlatCoefficientSupportPairMap Q T g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedAboveFlatCoefficientOpenSquare f g).symm

/-- Fine native ambient sections with their original auxiliary closed support. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:116"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
abbrev BoundedAboveFlatCoefficientSupportedAmbientSections (a : Under R) :=
  BoundedAboveFlatCoefficientSupportedSections (boundedAboveFlatCoefficientSupportOpen Q T a).ι

/-- Fine native open sections with support precisely on the actual intersection. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:120"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
abbrev BoundedAboveFlatCoefficientSupportedOpenSections (a : Under R) :=
  BoundedAboveFlatCoefficientSupportedSections (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι

/-- The unchanged actual coefficient functor on supported ambient native sections. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:124"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedAmbientMap {a b : Under R} (g : a ⟶ b) :
    BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a ⥤
      BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T b :=
  boundedAboveFlatCoefficientSupportedSectionsMap
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι (boundedAboveFlatCoefficientSupportOpen Q T
      b).ι
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    (boundedAboveFlatCoefficientSupportPairMap Q T g).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T g))

/-- The unchanged actual coefficient functor on the supported native open sections. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:134"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenMap {a b : Under R} (g : a ⟶ b) :
    BoundedAboveFlatCoefficientSupportedOpenSections f T a ⥤
      BoundedAboveFlatCoefficientSupportedOpenSections f T b :=
  boundedAboveFlatCoefficientSupportedSectionsMap
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T b).ι
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
    (boundedAboveFlatCoefficientOpenSupportPairMap f T g).left
    (by
      dsimp only [boundedAboveFlatCoefficientOpenSupportPairMap, supportedPairTargetSquare,
        supportOpenPair, MorphismProperty.Arrow.homMk]
      exact Scheme.Hom.resLE_comp_ι _ _)

/-- Restriction uses original joint reindexing with the literal inverse-image support square. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:148"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenRestriction (a : Under R) :
    BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a ⥤
      BoundedAboveFlatCoefficientSupportedOpenSections f T a :=
  boundedAboveFlatCoefficientSupportedSectionsMap
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
    (supportRestrictionPair (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a)).left
    (MorphismProperty.Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a)))

/-- The original supported restriction intertwines actual native evaluation and geometric pullback.
-/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:161"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
def boundedAboveFlatCoefficientSupportedOpenRestrictionEvaluationIso (a : Under R) :
    boundedAboveFlatCoefficientSupportedOpenRestriction f T a ⋙
        boundedAboveFlatCoefficientSupportedEvaluation (i := (op P, a))
          (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι ≅
      boundedAboveFlatCoefficientSupportedEvaluation (i := (op Q, a))
        (boundedAboveFlatCoefficientSupportOpen Q T a).ι ⋙
        boundedAboveFlatPerfectSupportedPullback
          (supportRestrictionPair (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a)) :=
  boundedAboveFlatCoefficientSupportedSectionReindexIso
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)
    (supportRestrictionPair (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a)).left
    (MorphismProperty.Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a)))

omit [IsOpenImmersion f.left] in
/-- The actual coefficient and restriction functors form a strict supported section square. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:179"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_square {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientSupportedAmbientMap T g ⋙
        boundedAboveFlatCoefficientSupportedOpenRestriction f T b =
      boundedAboveFlatCoefficientSupportedOpenRestriction f T a ⋙
        boundedAboveFlatCoefficientSupportedOpenMap f T g :=
  boundedAboveFlatCoefficientSupportedSectionsMap_square
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι
    (boundedAboveFlatCoefficientSupportOpen Q T b).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
    (boundedAboveFlatCoefficientOpenSupportOpen f T b).ι
    (i := (op Q, a)) (k := (op Q, b)) (k' := (op P, a)) (t := (op P, b))
    (𝟙 (op Q), g) (f.op, 𝟙 b) (f.op, 𝟙 a) (𝟙 (op P), g)
    (boundedAboveFlatCoefficientSupportPairMap Q T g).left
    (supportRestrictionPair (schemeMap f b) (boundedAboveFlatCoefficientSupportOpen Q T b)).left
    (supportRestrictionPair (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a)).left
    (boundedAboveFlatCoefficientOpenSupportPairMap f T g).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientSupportPairMap Q T g))
    (MorphismProperty.Arrow.w (supportRestrictionPair (schemeMap f b)
      (boundedAboveFlatCoefficientSupportOpen Q T b)))
    (MorphismProperty.Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a)))
    (by
      dsimp only [boundedAboveFlatCoefficientOpenSupportPairMap, supportedPairTargetSquare,
        supportOpenPair, MorphismProperty.Arrow.homMk]
      exact Scheme.Hom.resLE_comp_ι _ _)
    ((rowTransformation f).naturality g)

omit [IsOpenImmersion f.left] in
/-- The actual open-side support preimage is preserved by every coefficient map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:208"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientOpenSupportOpen_preimage {a b : Under R} (g : a ⟶ b) :
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
        (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g) ⁻¹ᵁ
          boundedAboveFlatCoefficientOpenSupportOpen f T a =
        boundedAboveFlatCoefficientOpenSupportOpen f T b := by
  rw [boundedAboveFlatCoefficientOpenSupportOpen_eq, boundedAboveFlatCoefficientOpenSupportOpen_eq]
  exact boundedAboveFlatCoefficientSupportOpen_preimage P (f.left ⁻¹ᵁ T) g

/-- The auxiliary support and the localization complement are the actual two closed factors. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:217"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientFiberSupportOpen_not_mem (a : Under R) (x : space (op Q, a)) :
    x ∉ boundedAboveFlatCoefficientFiberSupportOpen f T a ↔
      x ∉ boundedAboveFlatCoefficientSupportOpen Q T a ∧ x ∉ (schemeMap f a).opensRange :=
  not_or

/-- The actual native section category on the intersection of the two closed supports. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:223"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
abbrev BoundedAboveFlatCoefficientSupportedFiberSections (a : Under R) :=
  BoundedAboveFlatCoefficientSupportedSections (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι

/-- Inside auxiliary support, the original closed fiber support is exactly open acyclicity. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportRestriction.lean:227"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem boundedAboveFlatCoefficientFiberSupported_iff (a : Under R)
    (S : BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientFiberSupportOpen f T
      a).ι S.obj ↔
      (((restrictFunctor (schemeMap f a)).mapHomologicalComplex (.up ℤ)).obj
        ((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj S.obj).obj).Acyclic := by
  have h := boundedAboveFlatPerfectSupported_sup_opensRange_iff
    (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a)
    ((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj S.obj).obj
  constructor
  · intro hS
    exact (h.mp ⟨((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj S.obj).property,
      hS⟩).2
  · intro hS
    exact (h.mpr
      ⟨⟨((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj S.obj).property,
        S.property⟩, hS⟩).2

end AlgebraicGeometry.Scheme.Modules

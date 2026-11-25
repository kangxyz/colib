/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBinarySimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitTrackComposition
public import Colib.KTheory.Waldhausen.Iterated.UnitPrismNodes

/-!
# Actual unit-shifted references for the split geometric pullback

The postcomposition and precomposition tracks use the original normalized, intermediate, and
final pullbacks and their actual scalar automorphisms. Each prism retains the three distinct
shifted references and the two commuting equations, without choosing any higher filler.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace UnitTrackPostcompSimplex

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(Y, ⊤))ˣ)

/-- The actual source unit retains its original chosen-zero conjugation. -/
def sourceUnitIso : boundedAboveFlatPerfectNormalizedPullback (f ≫ g) ≅
    boundedAboveFlatPerfectNormalizedPullback (f ≫ g) :=
  (boundedAboveFlatPerfectPullbackNormalizationIso (f ≫ g)).symm ≪≫
    boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r) ≪≫
      boundedAboveFlatPerfectPullbackNormalizationIso (f ≫ g)

/-- The actual intermediate unit is normalized only after its original postwhiskering. -/
def middleUnitIso : BoundedFlatPerfectBinarySimplex.intermediate f g ≅
    BoundedFlatPerfectBinarySimplex.intermediate f g :=
  (CategoryTheory.rebaseFunctorIso _ _ _ _).symm ≪≫
    isoWhiskerRight (boundedAboveFlatPerfectPullbackUnitIso g r)
      (boundedAboveFlatPerfectPullback f) ≪≫
      CategoryTheory.rebaseFunctorIso _ _ _ _

/-- The final unit postwhiskers the already normalized original source unit. -/
def finalUnitIso :
    boundedAboveFlatPerfectNormalizedPullback g ⋙ boundedAboveFlatPerfectNormalizedPullback f ≅
      boundedAboveFlatPerfectNormalizedPullback g ⋙ boundedAboveFlatPerfectNormalizedPullback f :=
  isoWhiskerRight
    ((boundedAboveFlatPerfectPullbackNormalizationIso g).symm ≪≫
      boundedAboveFlatPerfectPullbackUnitIso g r ≪≫
      boundedAboveFlatPerfectPullbackNormalizationIso g)
      (boundedAboveFlatPerfectNormalizedPullback f)

/-- This is precisely the original normalized source transformation. -/
theorem sourceUnitIso_hom : (sourceUnitIso f g r).hom =
    Waldhausen.normalizedWeakTransformation (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
      (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
      (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g)
        (Units.map f.appTop.hom.toMonoidHom r)).hom := rfl

/-- This is precisely the original normalized middle transformation. -/
theorem middleUnitIso_hom : (middleUnitIso f g r).hom =
    Waldhausen.normalizedWeakTransformation
      ((boundedAboveFlatPerfectPullback_isExact g).comp (boundedAboveFlatPerfectPullback_isExact f))
      ((boundedAboveFlatPerfectPullback_isExact g).comp (boundedAboveFlatPerfectPullback_isExact f))
      (whiskerRight (boundedAboveFlatPerfectPullbackUnitIso g r).hom
        (boundedAboveFlatPerfectPullback f)) := rfl

/-- This is precisely the original final whiskered normalized transformation. -/
theorem finalUnitIso_hom : (finalUnitIso f g r).hom =
    whiskerRight (Waldhausen.normalizedWeakTransformation
      (boundedAboveFlatPerfectPullback_isExact g)
      (boundedAboveFlatPerfectPullback_isExact g) (boundedAboveFlatPerfectPullbackUnitIso g r).hom)
        (boundedAboveFlatPerfectNormalizedPullback f) := rfl

/-- The original geometric intertwining survives the exact chosen-zero normalization. -/
theorem geometric_unit :
    (BoundedFlatPerfectBinarySimplex.geometricIso f g).hom ≫ (middleUnitIso f g r).hom =
      (sourceUnitIso f g r).hom ≫ (BoundedFlatPerfectBinarySimplex.geometricIso f g).hom := by
  rw [BoundedFlatPerfectBinarySimplex.geometricIso_hom, middleUnitIso_hom, sourceUnitIso_hom]
  rw [← normalizedWeakTransformation_comp, ← normalizedWeakTransformation_comp]
  exact congrArg (Waldhausen.normalizedWeakTransformation
    (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
    ((boundedAboveFlatPerfectPullback_isExact g).comp (boundedAboveFlatPerfectPullback_isExact f)))
      (boundedAboveFlatPerfectPullbackUnitIso_comp f g r)

/-- The original left normalization naturality square is the second unit equation. -/
theorem normalization_unit :
    (middleUnitIso f g r).hom ≫ (BoundedFlatPerfectBinarySimplex.normalizationIso f g).hom =
      (BoundedFlatPerfectBinarySimplex.normalizationIso f g).hom ≫ (finalUnitIso f g r).hom := by
  rw [middleUnitIso_hom, finalUnitIso_hom]
  exact exactNormalizationCompIso_natural_left (boundedAboveFlatPerfectPullback_isExact g)
    (boundedAboveFlatPerfectPullback_isExact g) (boundedAboveFlatPerfectPullback_isExact f)
    (boundedAboveFlatPerfectPullbackUnitIso g r).hom

/-- The actual source unit in the unchanged small-model coordinates. -/
def sourceUnit : (BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor ≅
    (BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (sourceUnitIso f g r) AsSmall.up)

/-- The actual middle unit in the unchanged small-model coordinates. -/
def middleUnit : (BoundedFlatPerfectBinarySimplex.intermediateMap f g).hom.toFunctor ≅
    (BoundedFlatPerfectBinarySimplex.intermediateMap f g).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (middleUnitIso f g r) AsSmall.up)

/-- The actual final unit in the unchanged small-model coordinates. -/
def finalUnit : (BoundedFlatPerfectBinarySimplex.targetMap f g).hom.toFunctor ≅
    (BoundedFlatPerfectBinarySimplex.targetMap f g).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (finalUnitIso f g r) AsSmall.up)

/-- Full small-model geometric components satisfy the original commuting equation. -/
theorem small_geometric_unit :
    (BoundedFlatPerfectBinarySimplex.first f g).hom ≫ (middleUnit f g r).hom =
      (sourceUnit f g r).hom ≫ (BoundedFlatPerfectBinarySimplex.first f g).hom := by
  have h := congrArg (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (geometric_unit f g r)
  simpa only [BoundedFlatPerfectBinarySimplex.first, middleUnit, sourceUnit, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_comp, whiskerRight_comp] using h

/-- Full small-model normalization components satisfy the original commuting equation. -/
theorem small_normalization_unit :
    (middleUnit f g r).hom ≫ (BoundedFlatPerfectBinarySimplex.second f g).hom =
      (BoundedFlatPerfectBinarySimplex.second f g).hom ≫ (finalUnit f g r).hom := by
  have h := congrArg (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (normalization_unit f g r)
  simpa only [BoundedFlatPerfectBinarySimplex.second, middleUnit, finalUnit, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_comp, whiskerRight_comp] using h

/-- All six actual dependent nodes keep the three unit-shifted reference isomorphisms. -/
def nodes := UnitPrismNodes.nodes
  (BoundedFlatPerfectBinarySimplex.sourceMap f g)
  (BoundedFlatPerfectBinarySimplex.intermediateMap f g)
  (BoundedFlatPerfectBinarySimplex.targetMap f g) (BoundedFlatPerfectBinarySimplex.first f g)
  (BoundedFlatPerfectBinarySimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
  (finalUnit f g r)

/-- The actual common simplex has no supplied higher-comparison input. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/UnitTrackPostcompSimplex.lean:375-484"
  "adaptation" "Original split pullback reference prism with all normalized unit nodes"]
def simplex := UnitPrismNodes.simplex
  (BoundedFlatPerfectBinarySimplex.sourceMap f g)
  (BoundedFlatPerfectBinarySimplex.intermediateMap f g)
  (BoundedFlatPerfectBinarySimplex.targetMap f g) (BoundedFlatPerfectBinarySimplex.first f g)
  (BoundedFlatPerfectBinarySimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
  (finalUnit f g r)

end UnitTrackPostcompSimplex

namespace UnitTrackPrecompSimplex

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(X, ⊤))ˣ)

/-- The actual source unit retains its original chosen-zero conjugation. -/
def sourceUnitIso : boundedAboveFlatPerfectNormalizedPullback (f ≫ g) ≅
    boundedAboveFlatPerfectNormalizedPullback (f ≫ g) :=
  (boundedAboveFlatPerfectPullbackNormalizationIso (f ≫ g)).symm ≪≫
    boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) r ≪≫
      boundedAboveFlatPerfectPullbackNormalizationIso (f ≫ g)

/-- The actual intermediate unit is normalized only after its original prewhiskering. -/
def middleUnitIso : BoundedFlatPerfectBinarySimplex.intermediate f g ≅
    BoundedFlatPerfectBinarySimplex.intermediate f g :=
  (CategoryTheory.rebaseFunctorIso _ _ _ _).symm ≪≫
    isoWhiskerLeft (boundedAboveFlatPerfectPullback g)
      (boundedAboveFlatPerfectPullbackUnitIso f r) ≪≫
      CategoryTheory.rebaseFunctorIso _ _ _ _

/-- The final unit prewhiskers the already normalized original target unit. -/
def finalUnitIso :
    boundedAboveFlatPerfectNormalizedPullback g ⋙ boundedAboveFlatPerfectNormalizedPullback f ≅
      boundedAboveFlatPerfectNormalizedPullback g ⋙ boundedAboveFlatPerfectNormalizedPullback f :=
  isoWhiskerLeft (boundedAboveFlatPerfectNormalizedPullback g)
    ((boundedAboveFlatPerfectPullbackNormalizationIso f).symm ≪≫
      boundedAboveFlatPerfectPullbackUnitIso f r ≪≫
      boundedAboveFlatPerfectPullbackNormalizationIso f)

/-- This is precisely the original normalized source transformation. -/
theorem sourceUnitIso_hom : (sourceUnitIso f g r).hom =
    Waldhausen.normalizedWeakTransformation (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
      (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
      (boundedAboveFlatPerfectPullbackUnitIso (f ≫ g) r).hom := rfl

/-- This is precisely the original normalized middle transformation. -/
theorem middleUnitIso_hom : (middleUnitIso f g r).hom =
    Waldhausen.normalizedWeakTransformation
      ((boundedAboveFlatPerfectPullback_isExact g).comp (boundedAboveFlatPerfectPullback_isExact f))
      ((boundedAboveFlatPerfectPullback_isExact g).comp (boundedAboveFlatPerfectPullback_isExact f))
      (whiskerLeft (boundedAboveFlatPerfectPullback g)
        (boundedAboveFlatPerfectPullbackUnitIso f r).hom) := rfl

/-- This is precisely the original final whiskered normalized transformation. -/
theorem finalUnitIso_hom : (finalUnitIso f g r).hom =
    whiskerLeft (boundedAboveFlatPerfectNormalizedPullback g)
      (Waldhausen.normalizedWeakTransformation (boundedAboveFlatPerfectPullback_isExact f)
        (boundedAboveFlatPerfectPullback_isExact f)
        (boundedAboveFlatPerfectPullbackUnitIso f r).hom) := rfl

/-- The original geometric intertwining survives the exact chosen-zero normalization. -/
theorem geometric_unit :
    (BoundedFlatPerfectBinarySimplex.geometricIso f g).hom ≫ (middleUnitIso f g r).hom =
      (sourceUnitIso f g r).hom ≫ (BoundedFlatPerfectBinarySimplex.geometricIso f g).hom := by
  rw [BoundedFlatPerfectBinarySimplex.geometricIso_hom, middleUnitIso_hom, sourceUnitIso_hom]
  rw [← normalizedWeakTransformation_comp, ← normalizedWeakTransformation_comp]
  exact congrArg (Waldhausen.normalizedWeakTransformation
    (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
    ((boundedAboveFlatPerfectPullback_isExact g).comp (boundedAboveFlatPerfectPullback_isExact f)))
      (boundedAboveFlatPerfectPullbackUnitIso_comp_target f g r)

/-- The original right normalization naturality square is the second unit equation. -/
theorem normalization_unit :
    (middleUnitIso f g r).hom ≫ (BoundedFlatPerfectBinarySimplex.normalizationIso f g).hom =
      (BoundedFlatPerfectBinarySimplex.normalizationIso f g).hom ≫ (finalUnitIso f g r).hom := by
  rw [middleUnitIso_hom, finalUnitIso_hom]
  exact exactNormalizationCompIso_natural_right (boundedAboveFlatPerfectPullback_isExact g)
    (boundedAboveFlatPerfectPullback_isExact f) (boundedAboveFlatPerfectPullback_isExact f)
    (boundedAboveFlatPerfectPullbackUnitIso f r).hom

/-- The actual source unit in the unchanged small-model coordinates. -/
def sourceUnit : (BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor ≅
    (BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (sourceUnitIso f g r) AsSmall.up)

/-- The actual middle unit in the unchanged small-model coordinates. -/
def middleUnit : (BoundedFlatPerfectBinarySimplex.intermediateMap f g).hom.toFunctor ≅
    (BoundedFlatPerfectBinarySimplex.intermediateMap f g).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (middleUnitIso f g r) AsSmall.up)

/-- The actual final unit in the unchanged small-model coordinates. -/
def finalUnit : (BoundedFlatPerfectBinarySimplex.targetMap f g).hom.toFunctor ≅
    (BoundedFlatPerfectBinarySimplex.targetMap f g).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (finalUnitIso f g r) AsSmall.up)

/-- Full small-model geometric components satisfy the original commuting equation. -/
theorem small_geometric_unit :
    (BoundedFlatPerfectBinarySimplex.first f g).hom ≫ (middleUnit f g r).hom =
      (sourceUnit f g r).hom ≫ (BoundedFlatPerfectBinarySimplex.first f g).hom := by
  have h := congrArg (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (geometric_unit f g r)
  simpa only [BoundedFlatPerfectBinarySimplex.first, middleUnit, sourceUnit, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_comp, whiskerRight_comp] using h

/-- Full small-model normalization components satisfy the original commuting equation. -/
theorem small_normalization_unit :
    (middleUnit f g r).hom ≫ (BoundedFlatPerfectBinarySimplex.second f g).hom =
      (BoundedFlatPerfectBinarySimplex.second f g).hom ≫ (finalUnit f g r).hom := by
  have h := congrArg (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (normalization_unit f g r)
  simpa only [BoundedFlatPerfectBinarySimplex.second, middleUnit, finalUnit, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_comp, whiskerRight_comp] using h

/-- All six actual dependent nodes keep the three unit-shifted reference isomorphisms. -/
def nodes := UnitPrismNodes.nodes
  (BoundedFlatPerfectBinarySimplex.sourceMap f g)
  (BoundedFlatPerfectBinarySimplex.intermediateMap f g)
  (BoundedFlatPerfectBinarySimplex.targetMap f g) (BoundedFlatPerfectBinarySimplex.first f g)
  (BoundedFlatPerfectBinarySimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
  (finalUnit f g r)

/-- The actual common simplex has no supplied higher-comparison input. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/UnitTrackPrecompSimplex.lean:30-139"
  "adaptation" "Original split pullback reference prism with all normalized unit nodes"]
def simplex := UnitPrismNodes.simplex
  (BoundedFlatPerfectBinarySimplex.sourceMap f g)
  (BoundedFlatPerfectBinarySimplex.intermediateMap f g)
  (BoundedFlatPerfectBinarySimplex.targetMap f g) (BoundedFlatPerfectBinarySimplex.first f g)
  (BoundedFlatPerfectBinarySimplex.second f g) (sourceUnit f g r) (middleUnit f g r)
  (finalUnit f g r)

end UnitTrackPrecompSimplex

end AlgebraicGeometry.Scheme.Modules

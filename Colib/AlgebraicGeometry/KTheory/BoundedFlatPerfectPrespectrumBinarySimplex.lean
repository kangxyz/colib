/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumTripleSimplex
public import Colib.KTheory.Waldhausen.Iterated.NormalizationNaturality

/-!
# Binary simplex for chosen-zero normalized pullback

The actual geometric comparison and the subsequent normalization are separate edges.
The common triangle retains both time parameters of the prespectrum homotopy.

Adapted from Quillen `BoundedFlat/BinaryNormalizationSimplex.lean:24-126` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen
  CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry AlgebraicGeometry.RingedSpace
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectBinarySimplex

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "PE" => boundedAboveFlatPerfectPullback_isExact
local notation "PB" => boundedAboveFlatPerfectPullback
local notation "N" => boundedAboveFlatPerfectNormalizedPullback
local notation "NE" => boundedAboveFlatPerfectNormalizedPullback_exact
local notation "NZ" => boundedAboveFlatPerfectNormalizedPullback_obj_zero
local notation "NC" => boundedAboveFlatPerfectNormalizedPullbackCompIso
local notation "NCh" => boundedAboveFlatPerfectNormalizedPullbackCompIso_hom
local notation "PC" => boundedAboveFlatPerfectPullbackCompIso
local notation "NI" => boundedAboveFlatPerfectPullbackNormalizationIso

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The actual intermediate normalization of the unnormalized composite functor. -/
def intermediate : (boundedAboveFlatPerfectComplex Z.toRingedSpace).FullSubcategory ⥤
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  CategoryTheory.rebaseFunctor (PB g ⋙ PB f)
    (W Z).zero (W X).zero
    ((((PE g).comp (PE f)).zero
      (W Z).isZero).iso (W X).isZero)

/-- The old first transformation is the conjugated geometric isomorphism. -/
def geometricIso : N (f ≫ g) ≅ intermediate f g :=
  (NI (f ≫ g)).symm ≪≫
    PC f g ≪≫
    CategoryTheory.rebaseFunctorIso _ _ _ _

/-- This is exactly the first component used by the old binary comparison. -/
theorem geometricIso_hom : (geometricIso f g).hom =
    CategoryTheory.Waldhausen.normalizedWeakTransformation (PE (f ≫ g))
      ((PE g).comp (PE f))
      (PC f g).hom := rfl

/-- The old second component is the unchanged binary normalization isomorphism. -/
def normalizationIso : intermediate f g ≅
    N g ⋙ N f :=
  exactNormalizationCompIso (PE g)
    (PE f)

/-- The actual split composite is the native total normalized comparison. -/
theorem composite_hom : (geometricIso f g).hom ≫ (normalizationIso f g).hom =
    (NC f g).hom :=
  (NCh f g).symm

/-- The model map induced by normalized pullback along the composite scheme map `f ≫ g`. -/
def sourceMap : asSmallCategory (W Z) ⟶
    asSmallCategory (W X) :=
  asSmallCategoryMap (W Z) (W X) (NE (f ≫ g))
    (NZ _)

/-- The model map induced by rebasing the composite of the two unnormalized pullback functors. -/
def intermediateMap : asSmallCategory (W Z) ⟶
    asSmallCategory (W X) :=
  asSmallCategoryMap (W Z) (W X) ((PE g).comp
    (PE f)).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

/-- The model map induced by composing normalized pullback along `g` with normalized pullback
along `f`. -/
def targetMap : asSmallCategory (W Z) ⟶
    asSmallCategory (W X) :=
  asSmallCategoryMap (W Z) (W X) ((NE g).comp
    (NE f))
    (by simp only [comp_obj, NZ])

/-- The geometric comparison from the composite-map model functor to its rebased intermediate. -/
def first : (sourceMap f g).hom.toFunctor ≅ (intermediateMap f g).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (geometricIso f g) AsSmall.up)

/-- The normalization comparison from the rebased intermediate to the composite normalized model
functor. -/
def second : (intermediateMap f g).hom.toFunctor ≅ (targetMap f g).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight (normalizationIso f g) AsSmall.up)

/-- The total normalized pullback composition isomorphism transported to the model functors. -/
def total : (sourceMap f g).hom.toFunctor ≅ (targetMap f g).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down
    (isoWhiskerRight (NC f g) AsSmall.up)

/-- The original two transformations compose to the same normalized comparison. -/
theorem small_composite_hom : (first f g).hom ≫ (second f g).hom = (total f g).hom := by
  have hh := congrArg
    (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up)) (composite_hom f g)
  simpa only [first, second, total, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_comp, whiskerRight_comp] using hh

/-- All three actual binary vertices use the original total functor as common reference. -/
def simplex : ModelSimplex (asSmallCategory (W Z))
    (asSmallCategory (W X)) 2 :=
  ModelSimplex.ofIsos (sourceMap f g) ![sourceMap f g, intermediateMap f g, targetMap f g]
    (Fin.cases (Iso.refl _) (Fin.cases (first f g)
      (Fin.cases (total f g) (fun i ↦ Fin.elim0 i))))

/-- The complete old triangle, including both original normalization components. -/
theorem simplex_eq_triangle : simplex f g =
    ModelSimplex.triangle (F := sourceMap f g) (G := intermediateMap f g)
      (H := targetMap f g) (first f g).hom (second f g).hom
      (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
      (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) := by
  have he : simplex f g = (simplex f g).face (𝟙 ⦋2⦌) :=
    ModelSimplex.ext_diagram (by rfl)
  rw [he]
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact small_composite_hom f g

/-- Every point of the old composition triangle has an explicit common-simplex lift. -/
theorem whole_triangle (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W Z)).space n) :
    prespectrumSimplexFamily (simplex f g) n
      (CategoryTheory.TheoremB.compositionTriangleHomotopy (r, s), x) =
      (prespectrumTransformationCompositionHomotopy (F := sourceMap f g)
        (G := intermediateMap f g) (H := targetMap f g) (first f g).hom (second f g).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance)).level n (r, (s, x)) := by
  rw [simplex_eq_triangle]
  exact prespectrumSimplexFamily_triangle (F := sourceMap f g) (G := intermediateMap f g)
    (H := targetMap f g) _ _ _ _ n r s x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectBinarySimplex

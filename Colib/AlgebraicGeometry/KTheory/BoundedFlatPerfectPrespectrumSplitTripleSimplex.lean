/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBinarySimplex

/-!
# The split simplex for normalized geometric pullback associativity

The two normalized composition routes and all four binary normalization triangles are
faces of one simplex with eight vertices. The intermediate functors use the selected
zero normalization of the original unnormalized composites.

Adapted from Quillen `BoundedFlat/SplitTripleSimplex.lean:24-230` at
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
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleSimplex

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "source" => BoundedFlatPerfectTripleSimplex.source
local notation "left" => BoundedFlatPerfectTripleSimplex.left
local notation "right" => BoundedFlatPerfectTripleSimplex.right
local notation "target" => BoundedFlatPerfectTripleSimplex.target
local notation "PE" => boundedAboveFlatPerfectPullback_isExact
local notation "N" => boundedAboveFlatPerfectNormalizedPullback
local notation "NE" => boundedAboveFlatPerfectNormalizedPullback_exact
local notation "NZ" => boundedAboveFlatPerfectNormalizedPullback_obj_zero

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The first old binary intermediate on the left route. -/
abbrev leftFirstMap := BoundedFlatPerfectBinarySimplex.intermediateMap f (g ≫ h)

/-- The second old binary intermediate on the left route, postwhiskered by the actual map. -/
def leftSecondMap : asSmallCategory (W T) ⟶
    asSmallCategory (W X) :=
  asSmallCategoryMap (W T) (W X) (((PE h).comp
    (PE g)).rebase.comp (NE f))
    (by simp only [comp_obj, CategoryTheory.rebaseFunctor_obj_base,
      NZ])

/-- The first old binary intermediate on the right route. -/
abbrev rightFirstMap := BoundedFlatPerfectBinarySimplex.intermediateMap (f ≫ g) h

/-- The second old binary intermediate on the right route, prewhiskered by the actual map. -/
def rightSecondMap : asSmallCategory (W T) ⟶
    asSmallCategory (W X) :=
  asSmallCategoryMap (W T) (W X) ((NE h).comp
    ((PE g).comp (PE f)).rebase)
    (by simp only [comp_obj, NZ,
      CategoryTheory.rebaseFunctor_obj_base])

/-- The geometric comparison for the first left binary step, using `f` and `g ≫ h`. -/
abbrev leftFirstGeometric := BoundedFlatPerfectBinarySimplex.first f (g ≫ h)

/-- The normalization comparison for the first left binary step, using `f` and `g ≫ h`. -/
abbrev leftFirstNormalization := BoundedFlatPerfectBinarySimplex.second f (g ≫ h)

/-- The geometric comparison for `g` and `h`, postcomposed with normalized pullback along `f`. -/
def leftSecondGeometric : (left f g h).hom.toFunctor ≅
    (leftSecondMap f g h).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerRight (BoundedFlatPerfectBinarySimplex.geometricIso g h)
      (N f)) AsSmall.up)

/-- The normalization comparison for `g` and `h`, postwhiskered by pullback along `f`. -/
def leftSecondNormalization : (leftSecondMap f g h).hom.toFunctor ≅
    (target f g h).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerRight (BoundedFlatPerfectBinarySimplex.normalizationIso g h)
      (N f)) AsSmall.up)

/-- The geometric comparison for `f ≫ g` and `h`, after reassociating the composite pullback. -/
def rightFirstGeometric : (source f g h).hom.toFunctor ≅
    (rightFirstMap f g h).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg N (Category.assoc f g h).symm) ≪≫
      BoundedFlatPerfectBinarySimplex.geometricIso (f ≫ g) h) AsSmall.up)

/-- The normalization comparison for the first right binary step, using `f ≫ g` and `h`. -/
abbrev rightFirstNormalization := BoundedFlatPerfectBinarySimplex.second (f ≫ g) h

/-- The geometric comparison for `f` and `g`, precomposed with normalized pullback along `h`. -/
def rightSecondGeometric : (right f g h).hom.toFunctor ≅
    (rightSecondMap f g h).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerLeft (N h)
      (BoundedFlatPerfectBinarySimplex.geometricIso f g)) AsSmall.up)

/-- The normalization comparison for `f` and `g`, precomposed with normalized pullback along `h`. -/
def rightSecondNormalization : (rightSecondMap f g h).hom.toFunctor ≅
    (target f g h).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (isoWhiskerLeft (N h)
      (BoundedFlatPerfectBinarySimplex.normalizationIso f g)) AsSmall.up)

/-- The first split left pair composes to the first normalized left edge. -/
theorem left_first_composite :
    (leftFirstGeometric f g h).hom ≫ (leftFirstNormalization f g h).hom =
      (BoundedFlatPerfectTripleSimplex.leftFirst f g h).hom :=
  BoundedFlatPerfectBinarySimplex.small_composite_hom f (g ≫ h)

/-- The second split left pair composes to the second normalized left edge. -/
theorem left_second_composite :
    (leftSecondGeometric f g h).hom ≫ (leftSecondNormalization f g h).hom =
      (BoundedFlatPerfectTripleSimplex.leftSecond f g h).hom := by
  apply NatTrans.ext
  funext A
  simp only [leftSecondGeometric, leftSecondNormalization,
    BoundedFlatPerfectTripleSimplex.leftSecond,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.trans_hom, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id]
  rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app,
    BoundedFlatPerfectBinarySimplex.composite_hom]

/-- The scheme reassociation is preserved in the first right edge. -/
theorem right_first_composite :
    (rightFirstGeometric f g h).hom ≫ (rightFirstNormalization f g h).hom =
      (BoundedFlatPerfectTripleSimplex.rightFirst f g h).hom := by
  have hh := congrArg (fun η ↦ whiskerLeft AsSmall.down
    (whiskerRight (eqToHom
      (congrArg N (Category.assoc f g h).symm) ≫ η) AsSmall.up))
    (BoundedFlatPerfectBinarySimplex.composite_hom (f ≫ g) h)
  simpa only [rightFirstGeometric, rightFirstNormalization, BoundedFlatPerfectBinarySimplex.second,
    BoundedFlatPerfectTripleSimplex.rightFirst, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, eqToIso.hom, whiskerLeft_comp, whiskerRight_comp, Category.assoc] using hh

/-- The second split right pair composes to the second normalized right edge. -/
theorem right_second_composite :
    (rightSecondGeometric f g h).hom ≫ (rightSecondNormalization f g h).hom =
      (BoundedFlatPerfectTripleSimplex.rightSecond f g h).hom := by
  have hh := congrArg (fun η ↦ whiskerLeft AsSmall.down
    (whiskerRight (whiskerLeft (N h) η) AsSmall.up))
    (BoundedFlatPerfectBinarySimplex.composite_hom f g)
  simpa only [rightSecondGeometric, rightSecondNormalization,
    BoundedFlatPerfectTripleSimplex.rightSecond,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_comp, whiskerRight_comp] using hh

/-- The eight actual normalized and intermediate geometric functors. -/
def vertices : Fin 8 → (asSmallCategory (W T) ⟶
    asSmallCategory (W X)) :=
  ![source f g h, leftFirstMap f g h,
    left f g h, leftSecondMap f g h,
    rightFirstMap f g h, right f g h, rightSecondMap f g h,
    target f g h]

/-- Canonical comparisons from the same native total pullback to all eight vertices. -/
def references : ∀ i, (source f g h).hom.toFunctor ≅
    (vertices f g h i).hom.toFunctor :=
  Fin.cases (Iso.refl _) (Fin.cases (leftFirstGeometric f g h)
    (Fin.cases (BoundedFlatPerfectTripleSimplex.leftFirst f g h)
      (Fin.cases (BoundedFlatPerfectTripleSimplex.leftFirst f g h ≪≫ leftSecondGeometric f g h)
        (Fin.cases (rightFirstGeometric f g h)
          (Fin.cases (BoundedFlatPerfectTripleSimplex.rightFirst f g h)
            (Fin.cases (BoundedFlatPerfectTripleSimplex.rightFirst f g h ≪≫
              rightSecondGeometric f g h)
              (Fin.cases (BoundedFlatPerfectTripleSimplex.leftFirst f g h ≪≫
                BoundedFlatPerfectTripleSimplex.leftSecond f g h) (fun i ↦ Fin.elim0 i))))))))

/-- The common simplex contains every old binary and normalized triangle of the triple. -/
def simplex : ModelSimplex (asSmallCategory (W T))
    (asSmallCategory (W X)) 7 :=
  ModelSimplex.ofIsos (source f g h)
    (vertices f g h) (references f g h)

/-- An explicitly chosen ordered triple of vertices. -/
def triangleFace (i j k : Fin 8) (hij : i ≤ j) (hjk : j ≤ k) : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![i, j, k], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [le_trans hij hjk]⟩

/-- The first left binary triangle is the face on vertices 0, 1 and 2. -/
theorem left_first_face :
    (simplex f g h).face (triangleFace 0 1 2 (by decide) (by decide)) =
      ModelSimplex.triangle (F := source f g h) (G := leftFirstMap f g h) (H := left f g h)
        (leftFirstGeometric f g h).hom (leftFirstNormalization f g h).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact left_first_composite f g h

/-- The second left binary triangle is the face on vertices 2, 3 and 7. -/
theorem left_second_face :
    (simplex f g h).face (triangleFace 2 3 7 (by decide) (by decide)) =
      ModelSimplex.triangle (F := left f g h) (G := leftSecondMap f g h) (H := target f g h)
        (leftSecondGeometric f g h).hom (leftSecondNormalization f g h).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · rfl
  · change (_ ≫ (leftSecondGeometric f g h).hom) ≫ (leftSecondNormalization f g h).hom = _
    rw [Category.assoc, left_second_composite]
    rfl

/-- The total left route is the face on vertices 0, 2 and 7. -/
theorem normalized_left_face :
    (simplex f g h).face (triangleFace 0 2 7 (by decide) (by decide)) =
      ModelSimplex.triangle (F := source f g h) (G := left f g h) (H := target f g h)
        (BoundedFlatPerfectTripleSimplex.leftFirst f g h).hom
        (BoundedFlatPerfectTripleSimplex.leftSecond f g h).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · rfl

/-- The first right binary triangle is the face on vertices 0, 4 and 5. -/
theorem right_first_face :
    (simplex f g h).face (triangleFace 0 4 5 (by decide) (by decide)) =
      ModelSimplex.triangle (F := source f g h) (G := rightFirstMap f g h) (H := right f g h)
        (rightFirstGeometric f g h).hom (rightFirstNormalization f g h).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact right_first_composite f g h

/-- The second right binary triangle is the face on vertices 5, 6 and 7. -/
theorem right_second_face :
    (simplex f g h).face (triangleFace 5 6 7 (by decide) (by decide)) =
      ModelSimplex.triangle (F := right f g h) (G := rightSecondMap f g h) (H := target f g h)
        (rightSecondGeometric f g h).hom (rightSecondNormalization f g h).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · rfl
  · change (_ ≫ (rightSecondGeometric f g h).hom) ≫ (rightSecondNormalization f g h).hom = _
    rw [Category.assoc, right_second_composite]
    exact (BoundedFlatPerfectTripleSimplex.two_routes f g h).symm

/-- The total right route is the face on vertices 0, 5 and 7. -/
theorem normalized_right_face :
    (simplex f g h).face (triangleFace 0 5 7 (by decide) (by decide)) =
      ModelSimplex.triangle (F := source f g h) (G := right f g h) (H := target f g h)
        (BoundedFlatPerfectTripleSimplex.rightFirst f g h).hom
        (BoundedFlatPerfectTripleSimplex.rightSecond f g h).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) := by
  unfold simplex
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact (BoundedFlatPerfectTripleSimplex.two_routes f g h).symm

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleSimplex

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitUnitTriangleEvaluation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleRightFirst

/-! The two original first unit triangles recover the actual normalized pullback
composition tracks after their literal geometric identity transport.
Adapted from `OriginalUnitSquareSimplex.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "binaryFirst" => BoundedFlatPerfectBinarySimplex.first
local notation "binaryNativeApply" => BoundedFlatPerfectBinarySimplex.native_apply
local notation "binarySecond" => BoundedFlatPerfectBinarySimplex.second
local notation "binarySourceMap" => BoundedFlatPerfectBinarySimplex.sourceMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem whiskering_transport {C D E T : Type*}
    [Category* C] [Category* D] [Category* E] [Category* T]
    (L : C ⥤ D) (R : E ⥤ T) {F G : D ⥤ E} (e : F = G) :
    whiskerLeft L (whiskerRight (eqToHom e) R) =
      eqToHom (congrArg (fun H ↦ L ⋙ H ⋙ R) e) := by
  subst G
  ext A
  simp

private theorem right_source_map_eq : sourceMap f = binarySourceMap (𝟙 X) f := by
  apply WideSubcategory.hom_ext
  exact SmallWaldhausenCategory.Hom.ext (rightBinarySourceEq f)

private theorem right_first_hom :
    (rightFirstGeometric f).hom =
      eqToHom (rightBinarySourceEq f) ≫ (binaryFirst (𝟙 X) f).hom := by
  unfold rightFirstGeometric BoundedFlatPerfectBinarySimplex.first
  simp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.trans_hom, eqToIso.hom,
    whiskerRight_comp, whiskerLeft_comp, whiskering_transport]

/-- The first right unit triangle is the literal normalized binary comparison at every level. -/
theorem rightFirst_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightFirstParameter (r, t), x) =
      (boundedAboveFlatPerfectNormalizedCompTrackComparison (𝟙 X) f).level n (r, (t, x)) := by
  refine (rightFirstParameter_lift f n r t x).trans ?_
  let e := right_source_map_eq f
  let η := (binaryFirst (𝟙 X) f).hom
  let θ := (binarySecond (𝟙 X) f).hom
  let η' := eqToHom (congrArg (fun k : asSmallCategory (W Y) ⟶ asSmallCategory (W X) ↦
    k.hom.toFunctor) e) ≫ η
  have he : (rightFirstGeometric f).hom = η' := right_first_hom f
  have hη' : ∀ A, (W X).asSmall.weq (η'.app A) := by
    intro A
    exact he ▸ (W X).asSmall.weq_iso ((rightFirstGeometric f).hom.app A) inferInstance
  refine (triangle_congr_first_level (F := sourceMap f) (G := rightFirstMap f) (H := rightMap f)
    (rightFirstGeometric f).hom η' θ
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) hη'
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) he n r t x).trans ?_
  refine (triangle_source_transport_level (G := rightFirstMap f) (H := rightMap f) e η θ
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) hη' n r t x).trans ?_
  exact (binaryNativeApply (𝟙 X) f n r t x).symm

private theorem left_source_map_eq : sourceMap f = binarySourceMap f (𝟙 Y) := by
  apply WideSubcategory.hom_ext
  exact SmallWaldhausenCategory.Hom.ext (leftBinarySourceEq f)

private theorem left_first_hom :
    (leftFirstGeometric f).hom =
      eqToHom (leftBinarySourceEq f) ≫ (binaryFirst f (𝟙 Y)).hom := by
  unfold leftFirstGeometric BoundedFlatPerfectBinarySimplex.first
  simp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.trans_hom, eqToIso.hom,
    whiskerRight_comp, whiskerLeft_comp, whiskering_transport]

/-- The first left unit triangle is the literal normalized binary comparison at every level. -/
theorem leftFirst_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftFirstParameter (r, t), x) =
      (boundedAboveFlatPerfectNormalizedCompTrackComparison f (𝟙 Y)).level n (r, (t, x)) := by
  refine (leftFirstParameter_lift f n r t x).trans ?_
  let e := left_source_map_eq f
  let η := (binaryFirst f (𝟙 Y)).hom
  let θ := (binarySecond f (𝟙 Y)).hom
  let η' := eqToHom (congrArg (fun k : asSmallCategory (W Y) ⟶ asSmallCategory (W X) ↦
    k.hom.toFunctor) e) ≫ η
  have he : (leftFirstGeometric f).hom = η' := left_first_hom f
  have hη' : ∀ A, (W X).asSmall.weq (η'.app A) := by
    intro A
    exact he ▸ (W X).asSmall.weq_iso ((leftFirstGeometric f).hom.app A) inferInstance
  refine (triangle_congr_first_level (F := sourceMap f) (G := leftFirstMap f) (H := leftMap f)
    (leftFirstGeometric f).hom η' θ
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) hη'
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) he n r t x).trans ?_
  refine (triangle_source_transport_level (G := leftFirstMap f) (H := leftMap f) e η θ
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) hη' n r t x).trans ?_
  exact (binaryNativeApply f (𝟙 Y) n r t x).symm

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex

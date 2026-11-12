/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedSourceChange
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Whole constant-curve source changes

The actual pullback maps preserve both original projections. Both full boundary
components and their unreduced structure are retained. Adapted from the literal
source-map portions of `RelativeCurve/Constant/CurveSourceChange.lean` and
`BoundarySourceChange.lean` at motivic a6805c4a87cdfd7717dd7a94039246a167f15380.
No ideal-module or independent line-bundle model is imported.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {X S C K D Z : Scheme.{u}}
  (α : X ⟶ S) (q : S ⟶ K) (π : C ⟶ K) (qX : X ⟶ K) (h : qX = α ≫ q)
  (d : D ⟶ C) (z : Z ⟶ C)

/-- The infinity component changes only its source, retaining the whole boundary scheme. -/
def constantInfinitySourceMap :
    pullback (pullback.snd qX π) d ⟶ pullback (pullback.snd q π) d :=
  pullback.lift (pullback.fst _ _ ≫ retainedSourceChange q qX π α h.symm)
    (pullback.snd _ _) (by
      simp only [Category.assoc, retainedSourceChange_snd]
      exact pullback.condition)

@[reassoc (attr := simp)] theorem constantInfinitySourceMap_fst :
    constantInfinitySourceMap α q π qX h d ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ retainedSourceChange q qX π α h.symm := pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem constantInfinitySourceMap_snd :
    constantInfinitySourceMap α q π qX h d ≫ pullback.snd _ _ =
      pullback.snd _ _ := pullback.lift_snd _ _ _

/-- The full Z-product inclusion, using the original Z and its original structure map. -/
def constantBoundaryZeroMap (q : S ⟶ K) : pullback q (z ≫ π) ⟶ pullback q π :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ z)
    (by simp only [Category.assoc]; exact pullback.condition)

@[reassoc (attr := simp)] theorem constantBoundaryZeroMap_fst :
    constantBoundaryZeroMap π z q ≫ pullback.fst q π = pullback.fst _ _ :=
  pullback.lift_fst _ _ _
@[reassoc (attr := simp)] theorem constantBoundaryZeroMap_snd :
    constantBoundaryZeroMap π z q ≫ pullback.snd q π = pullback.snd _ _ ≫ z :=
  pullback.lift_snd _ _ _

/-- Exact compatibility of the zero-boundary component with source change. -/
theorem constantBoundaryZeroMap_source :
    retainedSourceChange q qX (z ≫ π) α h.symm ≫ constantBoundaryZeroMap π z q =
      constantBoundaryZeroMap π z qX ≫ retainedSourceChange q qX π α h.symm := by
  apply pullback.hom_ext <;> simp only [Category.assoc, constantBoundaryZeroMap_fst,
    constantBoundaryZeroMap_snd, retainedSourceChange_fst, retainedSourceChange_snd,
    constantBoundaryZeroMap_fst_assoc, retainedSourceChange_snd_assoc]

/-- The source change on the entire disjoint boundary, with neither component reduced. -/
def constantFullBoundarySourceMap :
    (pullback (pullback.snd qX π) d ⨿ pullback qX (z ≫ π)) ⟶
      (pullback (pullback.snd q π) d ⨿ pullback q (z ≫ π)) :=
  coprod.map (constantInfinitySourceMap α q π qX h d)
    (retainedSourceChange q qX (z ≫ π) α h.symm)

/-- The two original boundary inclusions commute with the actual ambient source change. -/
theorem constantFullBoundarySourceMap_inclusion :
    constantFullBoundarySourceMap α q π qX h d z ≫
      coprod.desc (pullback.fst _ _) (constantBoundaryZeroMap π z q) =
    coprod.desc (pullback.fst _ _) (constantBoundaryZeroMap π z qX) ≫
      retainedSourceChange q qX π α h.symm := by
  apply coprod.hom_ext
  · simp only [constantFullBoundarySourceMap, coprod.inl_map_assoc, coprod.inl_desc_assoc,
      coprod.inl_desc, constantInfinitySourceMap_fst]
  · simp only [constantFullBoundarySourceMap, coprod.inr_map_assoc,
      coprod.inr_desc_assoc, coprod.inr_desc]
    exact constantBoundaryZeroMap_source α q π qX h z

end AlgebraicGeometry.Scheme.RelativeCurvePencil

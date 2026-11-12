/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CommonBoundaryGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedBoundaryCover
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# The literal retained graph and the two independent source changes

Restriction of the second factor commutes with change of the first factor.
The actual graph of the retained target map is the full Cartesian inverse image
of the compactification graph. These statements preserve both literal maps and
all nilpotents; no graph-ideal equality is assumed as producer input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X X' C V : Scheme.{u}} (q : X ⟶ S) (q' : X' ⟶ S)
  (π : C ⟶ S) (f : X' ⟶ X) (hf : f ≫ q = q') (v : V ⟶ C)

/-- Changing the first factor commutes with retaining the second factor. -/
theorem retainedSourceChange_restrict_second :
    retainedProductInclusion q' π v ≫ retainedSourceChange q q' π f hf =
      retainedSourceChange q q' (v ≫ π) f hf ≫ retainedProductInclusion q π v := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, retainedSourceChange_fst, retainedSourceChange_snd,
      retainedProductInclusion_fst, retainedProductInclusion_snd,
      retainedProductInclusion_fst_assoc, retainedSourceChange_snd_assoc]

/-- The exact whole ideal comparison on the two commuting products. -/
theorem retainedSourceChange_restrict_ideal (I : (pullback q π).IdealSheafData) :
    (I.comap (retainedSourceChange q q' π f hf)).comap (retainedProductInclusion q' π v) =
      (I.comap (retainedProductInclusion q π v)).comap
        (retainedSourceChange q q' (v ≫ π) f hf) := by
  rw [← IdealSheafData.comap_comp, ← IdealSheafData.comap_comp,
    retainedSourceChange_restrict_second]

variable {Y B : Scheme.{u}} (j : Y ⟶ C) (α : B ⟶ Y)
  (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)

include hφ in
/-- The actual retained target map is over the unchanged common source base. -/
theorem retainedTarget_base : φ ≫ (v ≫ π) = commonProjection π j α := by
  rw [← Category.assoc, hφ, Category.assoc]

local notation "qB" => commonProjection π j α
local notation "G" => relativeGraph qB (v ≫ π) φ (retainedTarget_base π v j α φ hφ)
local notation "rB" => retainedProductInclusion qB π v
local notation "gA" => commonToLambda π j α

/-- The original compactification graph pulls back to the literal retained graph.
Only the actual factorization through the retained open is used. -/
theorem retainedGraph_compactification_isPullback [IsOpenImmersion v] :
    IsPullback G α (rB ≫ gA) (compactificationGraph π j) := by
  have hrf : rB ≫ gA ≫ pullback.fst (j ≫ π) π = pullback.fst qB (v ≫ π) ≫ α := by
    simp only [commonToLambda, retainedSourceChange_fst,
      retainedProductInclusion_fst_assoc]
  have hrs : rB ≫ gA ≫ pullback.snd (j ≫ π) π = pullback.snd qB (v ≫ π) ≫ v := by
    simp only [commonToLambda, retainedSourceChange_snd,
      retainedProductInclusion_snd]
  have hgf : compactificationGraph π j ≫ pullback.fst (j ≫ π) π = 𝟙 Y :=
    relativeGraph_fst (j ≫ π) π j rfl
  have hgs : compactificationGraph π j ≫ pullback.snd (j ≫ π) π = j :=
    relativeGraph_snd (j ≫ π) π j rfl
  refine { w := ?_, isLimit' := ?_ }
  · apply pullback.hom_ext
    · simp only [Category.assoc, hgf, Category.comp_id, hrf,
        relativeGraph_fst_assoc]
    · simp only [Category.assoc, hgs, hrs, relativeGraph_snd_assoc]
      exact hφ
  · refine ⟨PullbackCone.isLimitAux' _ (fun t ↦ ?_)⟩
    have hfst : t.fst ≫ pullback.fst qB (v ≫ π) ≫ α = t.snd := by
      have hh := congrArg (fun m ↦ m ≫ pullback.fst (j ≫ π) π) t.condition
      simpa only [Category.assoc, hgf, Category.comp_id, hrf] using hh
    have hsnd : t.fst ≫ pullback.snd qB (v ≫ π) ≫ v = t.snd ≫ j := by
      have hh := congrArg (fun m ↦ m ≫ pullback.snd (j ≫ π) π) t.condition
      simpa only [Category.assoc, hgs, hrs] using hh
    refine ⟨t.fst ≫ pullback.fst qB (v ≫ π), ?_, hfst, ?_⟩
    · change (t.fst ≫ pullback.fst qB (v ≫ π)) ≫ G = t.fst
      apply pullback.hom_ext
      · simp only [Category.assoc, relativeGraph_fst, Category.comp_id]
      · simp only [Category.assoc, relativeGraph_snd]
        apply (cancel_mono v).1
        calc
          (t.fst ≫ pullback.fst qB (v ≫ π) ≫ φ) ≫ v =
              (t.fst ≫ pullback.fst qB (v ≫ π) ≫ α) ≫ j := by
                simp only [Category.assoc, hφ]
          _ = t.snd ≫ j := by rw [hfst]
          _ = (t.fst ≫ pullback.snd qB (v ≫ π)) ≫ v := by
            simpa only [Category.assoc] using hsnd.symm
    · intro m hm _
      change m ≫ G = t.fst at hm
      have hh := congrArg (fun e ↦ e ≫ pullback.fst qB (v ≫ π)) hm
      simpa only [Category.assoc, relativeGraph_fst, Category.comp_id] using hh

/-- The complete pulled-back graph kernel is the actual retained graph ideal. -/
theorem retainedGraph_compactification_ideal [IsSeparated π] [IsOpenImmersion v] :
    ((compactificationGraph π j).ker.comap gA).comap rB =
      relativeGraphIdeal qB (v ≫ π) φ (retainedTarget_base π v j α φ hφ) := by
  rw [← IdealSheafData.comap_comp]
  exact (ker_eq_comap_of_cartesian
    (retainedGraph_compactification_isPullback π v j α φ hφ)).symm

end AlgebraicGeometry.Scheme.RelativeCurvePencil

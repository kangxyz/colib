/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Divisors.FiniteFlat
public import Colib.AlgebraicGeometry.Divisors.SectionKernelDifferencePullback

/-!
# The actual section-kernel correspondence is the original graph

The section's full image scheme is isomorphic to its source through the native `toImage` map.
Its composite to the original source-target product is proved to be the literal graph map.
The fundamental-cycle pushforward comparison therefore gives the original graph correspondence.
Reducedness of the source supplies length one; no reduction of the section kernel is taken.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {C X Y S : Scheme.{u}}
  (p : X ⟶ S) (t : Y ⟶ S) (r : C ⟶ pullback p t)
  (s : X ⟶ C) (hs : s ≫ (r ≫ pullback.fst p t) = 𝟙 X)

include hs in
/-- The original target map of the section has the required original base compatibility. -/
theorem sectionTarget_base : (s ≫ r ≫ pullback.snd p t) ≫ t = p := by
  calc
    (s ≫ r ≫ pullback.snd p t) ≫ t = (s ≫ (r ≫ pullback.fst p t)) ≫ p := by
      simp only [Category.assoc, pullback.condition]
    _ = p := by rw [hs, Category.id_comp]

/-- The actual composite from the original section source is the source-first graph map. -/
theorem section_comp_sourceTargetMap :
    s ≫ r = correspondenceGraphMap p t (s ≫ r ≫ pullback.snd p t)
      (sectionTarget_base p t r s hs) := by
  apply pullback.hom_ext
  · simpa only [Category.assoc, correspondenceGraphMap_fst] using hs
  · simp only [Category.assoc, correspondenceGraphMap_snd]

include hs in
/-- The whole section image projects isomorphically onto the original source. -/
theorem sectionKernelProjection_isIso [IsSeparated (r ≫ pullback.fst p t)] :
    IsIso ((s.ker.subschemeι ≫ r) ≫ pullback.fst p t) := by
  rw [Category.assoc]
  exact Stacks.Divisors.sectionKernelStructureMap_isIso (r ≫ pullback.fst p t) s hs

variable [IsNoetherian C] [IsNoetherian X] [IsReduced X]
  [IsSeparated t] [LocallyOfFiniteType t] [IsSeparated (r ≫ pullback.fst p t)]

local instance sectionSubschemeNoetherian : IsNoetherian s.ker.subscheme :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian s.ker.subschemeι
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace s.ker.subschemeι }

/-- Transport through the actual full image-scheme isomorphism gives the existing graph,
whose component weights are one because the original source is reduced. -/
@[colib_tag "COL-1051"]
theorem finiteFlatDivisorCorrespondence_sectionKernel :
    let := sectionKernelProjection_isIso p t r s hs
    finiteFlatDivisorCorrespondence p t r s.ker =
      graphCorrespondenceOfComponents p t (s ≫ r ≫ pullback.snd p t)
        (sectionTarget_base p t r s hs)
        (AlgebraicCycle.fundamentalCycle_genericPoints_finite X) := by
  let := sectionKernelProjection_isIso p t r s hs
  have : IsClosedImmersion (s ≫ (r ≫ pullback.fst p t)) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s (r ≫ pullback.fst p t)
  have : IsFinite (s.ker.subschemeι ≫ r) := IsFinite.of_comp _ (pullback.fst p t)
  have hfactor : s.toImage ≫ (s.ker.subschemeι ≫ r) =
      correspondenceGraphMap p t (s ≫ r ≫ pullback.snd p t)
        (sectionTarget_base p t r s hs) := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact section_comp_sourceTargetMap p t r s hs
  apply Subtype.ext
  rw [finiteFlatDivisorCorrespondence_val,
    ← finiteCyclePushforward_fundamentalCycle_iso (asIso s.toImage),
    finiteCyclePushforward_comp_apply]
  change noetherianCyclePushforward (s.toImage ≫ (s.ker.subschemeι ≫ r))
    (AlgebraicCycle.fundamentalCycle X) = _
  rw [hfactor]
  exact finiteCyclePushforward_fundamentalCycle_graph p t _ _

end Stacks.Chow

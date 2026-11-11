/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionWaldhausen
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenStructure

/-!
# Original relative-open weak equivalences of affine sections

The original section category keeps its cofibrations and chosen zero. Weak equivalences
are detected by actual original evaluation into the existing bounded-flat relative-open
model. The original support predicate makes the unique zero-to-section transformation
weak after restriction, without any assumption about the full open K₀ endpoint.
-/
@[expose] public section

open CategoryTheory.Waldhausen

open AlgebraicGeometry.RingedSpace

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules
open Waldhausen Fibration
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation

/-- The unique arrow from the original section zero to each original supported section. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionOpenWeak.lean:35-41"
  "adaptation" "The actual zero-to-support-inclusion natural transformation"]
def boundedAboveFlatAffineSupportedSectionZeroToOpen :
    (Functor.const (BoundedAboveFlatAffineSupportedSections j)).obj
        (boundedAboveFlatAffineSectionWaldhausen R).zero ⟶
      (boundedAboveFlatAffineSectionSupported j).ι where
  app s := (boundedAboveFlatAffineSectionWaldhausen R).isZero.to_ s.obj
  naturality _ _ _ := (boundedAboveFlatAffineSectionWaldhausen R).isZero.eq_of_src _ _

/-- Actual support proves weakness of the entire original zero-to-inclusion transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionOpenWeak.lean:44-58"
  "adaptation" "Support proves coarse weakness of the original zero arrow"]
theorem boundedAboveFlatAffineSupportedSectionZeroToOpen_weak
    (s : BoundedAboveFlatAffineSupportedSections j) :
    (boundedAboveFlatAffineSectionOpenWaldhausen j).weq
      ((boundedAboveFlatAffineSupportedSectionZeroToOpen j).app s) := by
  have hZ : IsZero (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((boundedAboveFlatAffineOriginalEvaluation R).obj
        (boundedAboveFlatAffineSectionWaldhausen R).zero).obj) :=
    ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
      ((boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).ι.map_isZero
      ((boundedAboveFlatAffineOriginalEvaluation_exact R).zero
        (boundedAboveFlatAffineSectionWaldhausen R).isZero))
  change QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((boundedAboveFlatAffineOriginalEvaluation R).map
      ((boundedAboveFlatAffineSupportedSectionZeroToOpen j).app s)).hom)
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt _ n (HomologicalComplex.acyclic_of_isZero _ hZ n)).mpr
    (s.property n)

end AlgebraicGeometry.Scheme.Modules

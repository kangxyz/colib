/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectGlobalUnit
public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreeFlat
public import Colib.AlgebraicGeometry.Modules.StructureSingleGlobalScalar
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitAction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite

/-! # The same rank-one structure single in native bounded-flat perfect complexes

The existing finite-free unit sheaf gives the original bounded vector-bundle single;
the existing literal flat inclusion supplies its bounded-flat evidence. The actual scalar
single agrees with the native degreewise unit action. No new perfect category is introduced.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open Stacks.Perfect.BoundedLocallyFreeComplexes
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The unchanged structure-sheaf complex in degree zero with its proved bounded-flat property. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    RankOne.lean:32-38"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def boundedAboveFlatRankOne (X : Scheme.{u}) :
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory := by
  let M := SheafOfModules.unit X.ringCatSheaf
  have hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
      (Stacks.SheafOfModules.Site.freePUnitIso (R := X.ringCatSheaf))
  exact ⟨(rankOnePerfectComplex X).obj,
    boundedAboveFlatPerfectComplex_of_boundedFiniteLocallyFree
      (boundedFiniteLocallyFreeComplex_single_obj M 0 hM)⟩

/-- The original inclusion retains exactly the already-defined rank-one perfect complex. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    RankOne.lean:41-42"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem boundedAboveFlatRankOne_inclusion (X : Scheme.{u}) :
    (boundedAboveFlatPerfectInclusion X.toRingedSpace).obj (boundedAboveFlatRankOne X) =
      rankOnePerfectComplex X := rfl

/-- The genuine degree-zero single of multiplication by the chosen unit. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    RankOne.lean:45-48"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def boundedAboveFlatRankOneUnit (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    boundedAboveFlatRankOne X ≅ boundedAboveFlatRankOne X :=
  (boundedAboveFlatPerfectComplex X.toRingedSpace).isoMk
    ((CochainComplex.singleFunctor X.Modules 0).mapIso (tensorCoefficientUnitIso X r))

/-- The degree-zero coefficient automorphism is the original forward scalar on the same object. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    RankOne.lean:51-59"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem boundedAboveFlatRankOneUnit_global (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    boundedAboveFlatRankOneUnit X r =
      (boundedAboveFlatPerfectGlobalUnitIso X r).app (boundedAboveFlatRankOne X) := by
  apply Iso.ext
  apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
  change _ = (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
    ((boundedAboveFlatPerfectGlobalUnitIso X r).hom.app (boundedAboveFlatRankOne X))
  rw [boundedAboveFlatPerfectGlobalUnitIso_hom_original]
  exact single_structureScalar_eq_globalScalar X (r : Γ(X, ⊤))

end AlgebraicGeometry.Scheme.Modules

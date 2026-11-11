/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectGlobalScalar
public import Colib.AlgebraicGeometry.Modules.PerfectRankOne

/-! # The native global scalar on the unchanged structure-sheaf single

This is the original single-map naturality proof. The module scalar is already the native
globalSmulCenter used by the tensor coefficient unit, so no second scalar action is introduced.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.RegularSequence (globalSmulCenter)
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The degree-zero single of a global scalar is the native scalar on the rank-one complex. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/\
    GlobalScalarSingle.lean:37-52"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem single_structureScalar_eq_globalScalar (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    (CochainComplex.singleFunctor X.Modules 0).map ((globalSmulCenter X r).app
      (SheafOfModules.unit X.ringCatSheaf)) =
      (complexGlobalScalar X r).app (rankOnePerfectComplex X).obj := by
  apply HomologicalComplex.from_single_hom_ext
  change ((HomologicalComplex.single X.Modules (.up ℤ) 0).map ((globalSmulCenter X r).app
      (SheafOfModules.unit X.ringCatSheaf))).f 0 =
    (globalSmulCenter X r).app
      (((HomologicalComplex.single X.Modules (.up ℤ) 0).obj
        (SheafOfModules.unit X.ringCatSheaf)).X 0)
  rw [HomologicalComplex.single_map_f_self]
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
    (SheafOfModules.unit X.ringCatSheaf)
  change e.hom ≫ (globalSmulCenter X r).app _ ≫ e.inv =
    (globalSmulCenter X r).app _
  rw [← cancel_mono e.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ((globalSmulCenter X r).naturality e.hom).symm


end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularTensorQuotient
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalSection

/-!
# The regular quotient is the original meromorphic tensor quotient

Only the comparison with a generic stalk uses integrality. The ordinary quotient is the
unchanged section constructed over the original open in `RegularTensorQuotient`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) [IsIntegral X] (L N : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

local instance regularQuotientQuasicoherent (F : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property F] : F.IsQuasicoherent :=
  isQuasicoherent_of_isInvertible F

local instance regularQuotientTensorInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (tensorObj L N) := by
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (inferInstance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (inferInstance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N)
  exact (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
    L N).toAlgebraicGeometry

/-- The original regular quotient on a generic-point neighbourhood represents precisely
COL-1047's meromorphic quotient, not a new section with the same divisor class. -/
@[colib_tag "COL-1052"]
theorem meromorphicGenericValue_quotient_eq_germ_regularTensorQuotient
    (b : N.sections) (hb : b.eval (op (⊤ : X.Opens)) ≠ 0) (U : X.Opens)
    [IsIso ((N.unitHomEquiv.symm b).over U)] (hU : genericPoint X ∈ U)
    (a : Γ(tensorObj L N, ⊤)) :
    meromorphicGenericValue X L
      (quotientTensorMeromorphicSection X L N
        (meromorphicSectionOfGlobalSection (tensorObj L N) a)
        (meromorphicSectionOfGlobalSection N (b.eval (op ⊤)))
        (isRegularMeromorphicSection_meromorphicSectionOfGlobalSection N _ hb)) =
      L.presheaf.germ U (genericPoint X) hU
        (regularTensorQuotientOnOpen X L N b U
          ((tensorObj L N).presheaf.map (homOfLE le_top).op a)) := by
  rw [quotientTensorMeromorphicSection,
    meromorphicGenericValue_meromorphicSectionOfConstantGenericStalk]
  apply (LinearEquiv.symm_apply_eq _).2
  have hbGerm : N.presheaf.germ U (genericPoint X) hU (b.eval (op U)) =
      N.presheaf.germ ⊤ (genericPoint X) trivial (b.eval (op ⊤)) :=
    Stacks.SheafOfModules.grpGerm_eval (X := X.toRingedSpace) b (genericPoint X) U hU
  let m := regularTensorQuotientOnOpen X L N b U
    ((tensorObj L N).presheaf.map (homOfLE le_top).op a)
  have hproduct : tensorStalkTmul L N (genericPoint X)
      (L.presheaf.germ U (genericPoint X) hU m)
      (N.presheaf.germ ⊤ (genericPoint X) trivial (b.eval (op ⊤))) =
      (tensorObj L N).presheaf.germ ⊤ (genericPoint X) trivial a := by
    refine (congrArg (fun z => tensorStalkTmul L N (genericPoint X)
      (L.presheaf.germ U (genericPoint X) hU m) z) hbGerm.symm).trans ?_
    refine (tensorStalkTmul_germ L N (genericPoint X) U hU m _).trans ?_
    change (tensorObj L N).presheaf.germ U (genericPoint X) hU
      (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U) L N
        m (b.eval (op U))) = _
    refine (congrArg ((tensorObj L N).presheaf.germ U (genericPoint X) hU)
      (tensorSection_regularTensorQuotientOnOpen X L N b U _)).trans ?_
    exact (tensorObj L N).presheaf.germ_res_apply (homOfLE le_top) (genericPoint X) hU a
  refine (meromorphicGenericValue_meromorphicSectionOfGlobalSection (tensorObj L N) a).trans
    (hproduct.symm.trans ?_)
  refine (congrArg (fun z => tensorStalkTmul L N (genericPoint X)
    (L.presheaf.germ U (genericPoint X) hU m) z)
    (meromorphicGenericValue_meromorphicSectionOfGlobalSection N (b.eval (op ⊤))).symm).trans ?_
  exact (tensorStalkRightBasisEquiv_apply L N (genericPoint X) _ _ _).symm

end AlgebraicGeometry.Scheme.Modules

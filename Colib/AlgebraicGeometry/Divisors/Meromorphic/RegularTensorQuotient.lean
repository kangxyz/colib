/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections.TensorRestriction
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorQuotient

/-!
# Regular tensor division on the original nonvanishing open

An ordinary section `b` trivializes its invertible module on its actual nonvanishing open.
The native restriction/tensor comparison and this trivialization give division of sections
of `L ⊗ N` by `b`, without any integrality or reducedness hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.Invertible

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf
  SheafOfModules.forget PresheafOfModules.restrictScalars
  AlgebraicGeometry.SheafedSpace.sheaf

attribute [local instance_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) (L N : X.Modules) (b : N.sections) (U : X.Opens)

/-- Division by the original section on any open where its multiplication map is an
isomorphism, using the native comparison between restriction and tensor product. -/
def tensorSectionQuotientIsoOver [h : IsIso ((N.unitHomEquiv.symm b).over U)] :
    (tensorObj L N).over U ≅ L.over U := by
  let O := (X.sheaf.over U).obj
  let hO := (Presheaf.isSheaf_iff_isSheaf_comp
    ((Opens.grothendieckTopology X).over U) O (forget₂ CommRingCat RingCat)).mp
      (X.sheaf.over U).property
  let e := @asIso _ _ _ _ ((N.unitHomEquiv.symm b).over U) h
  exact Stacks.SheafOfModules.tensorRestrictionIsoOnScheme X L N U ≪≫
    (tensorProductIso O hO (Iso.refl (L.over U)) e).symm ≪≫
      tensorProductRightUnitor O hO (L.over U)

/-- The actual ordinary quotient section on the unchanged open. -/
def regularTensorQuotientOnOpen [IsIso ((N.unitHomEquiv.symm b).over U)]
    (a : Γ(tensorObj L N, U)) : Γ(L, U) :=
  (tensorSectionQuotientIsoOver X L N b U).hom.val.app (op (Over.mk (𝟙 U))) a

/-- The inverse comparison is tensoring by the original section, without changing its
value by a frame scalar. -/
theorem tensorSectionQuotientIsoOver_inv_apply [IsIso ((N.unitHomEquiv.symm b).over U)]
    (m : Γ(L, U)) :
    (tensorSectionQuotientIsoOver X L N b U).inv.val.app (op (Over.mk (𝟙 U))) m =
      Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
        L N m (b.eval (op U)) := by
  let O := (X.sheaf.over U).obj
  let hO := (Presheaf.isSheaf_iff_isSheaf_comp
    ((Opens.grothendieckTopology X).over U) O (forget₂ CommRingCat RingCat)).mp
      (X.sheaf.over U).property
  let e := asIso ((N.unitHomEquiv.symm b).over U)
  change (Stacks.SheafOfModules.tensorRestrictionIsoOnScheme X L N U).inv.val.app
    (op (Over.mk (𝟙 U)))
      ((tensorProductIso O hO (Iso.refl (L.over U)) e).hom.val.app
        (op (Over.mk (𝟙 U)))
        ((tensorProductRightUnitor O hO (L.over U)).inv.val.app
          (op (Over.mk (𝟙 U))) m)) = _
  refine (congrArg
    (fun z => (Stacks.SheafOfModules.tensorRestrictionIsoOnScheme X L N U).inv.val.app
      (op (Over.mk (𝟙 U)))
      ((tensorProductIso O hO (Iso.refl (L.over U)) e).hom.val.app
        (op (Over.mk (𝟙 U))) z))
    (Stacks.SheafOfModules.tensorSections_rightUnitorInvAt O hO (L.over U)
      (op (Over.mk (𝟙 U))) m)).trans ?_
  refine (congrArg
    (fun z => (Stacks.SheafOfModules.tensorRestrictionIsoOnScheme X L N U).inv.val.app
      (op (Over.mk (𝟙 U))) z)
    (Stacks.SheafOfModules.tensorSections_tensorProductIsoAt O hO (op (Over.mk (𝟙 U)))
      (L.over U) (L.over U) (SheafOfModules.unit _) (N.over U)
      (Iso.refl (L.over U)) e m (1 : O.obj (op (Over.mk (𝟙 U)))))).trans ?_
  have he : e.hom.val.app (op (Over.mk (𝟙 U))) (1 : O.obj (op (Over.mk (𝟙 U)))) =
      b.eval (op U) := by
    change (1 : Γ(X, U)) • b.eval (op U) = b.eval (op U)
    exact one_smul _ _
  refine (congrArg
    (fun z => (Stacks.SheafOfModules.tensorRestrictionIsoOnScheme X L N U).inv.val.app
      (op (Over.mk (𝟙 U)))
      (Stacks.SheafOfModules.tensorSectionsAt O hO (op (Over.mk (𝟙 U)))
        (L.over U) (N.over U) m z)) he).trans ?_
  exact Stacks.SheafOfModules.tensorRestrictionIso_inv_tensorAt X L N U m (b.eval (op U))

/-- The regular quotient times the original denominator is the original numerator on
this whole open, including all nilpotents. -/
theorem tensorSection_regularTensorQuotientOnOpen
    [IsIso ((N.unitHomEquiv.symm b).over U)]
    (a : Γ(tensorObj L N, U)) :
    Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U) L N
      (regularTensorQuotientOnOpen X L N b U a)
      (b.eval (op U)) = a := by
  rw [← tensorSectionQuotientIsoOver_inv_apply]
  exact congrArg (fun f => f.val.app (op (Over.mk (𝟙 U))) a)
    (tensorSectionQuotientIsoOver X L N b U).hom_inv_id

variable [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]

/-- The ordinary tensor quotient on the original nonvanishing open of the denominator.
The native nonvanishing-section theorem supplies the isomorphism, rather than a caller. -/
def regularTensorQuotientOnNonvanishingOpen (a : Γ(tensorObj L N, ⊤)) :
    Γ(L, Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) N b) := by
  letI := Stacks.SheafOfModules.Scheme.isIso_over_nonvanishingOpen X N b
  exact regularTensorQuotientOnOpen X L N b
    (Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) N b)
    ((tensorObj L N).presheaf.map (homOfLE le_top).op a)

/-- On the entire nonvanishing open, the constructed quotient has the original numerator
and denominator. This statement has no reducedness, integrality, or Noetherianity hypothesis. -/
@[colib_tag "COL-1052",
  stacks 01CY "Native trivialization gives ordinary tensor division on the nonvanishing open",
  colib_ref "axiom_stacks_5ed82d14"
    "Algebra/Category/ModuleCat/Sheaf/NonvanishingSections/TensorRestriction.lean:424-463"
    "ingredient" "Restriction-tensor comparison computes the original pure tensor",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/NonvanishingTrivialization/Basic.lean:244-249"
    "ingredient" "The original section trivializes its module on its nonvanishing open"]
theorem tensorSection_regularTensorQuotientOnNonvanishingOpen
    (a : Γ(tensorObj L N, ⊤)) :
    let V := Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) N b
    Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op V) L N
      (regularTensorQuotientOnNonvanishingOpen X L N b a) (b.eval (op V)) =
      (tensorObj L N).presheaf.map (homOfLE le_top).op a := by
  let := Stacks.SheafOfModules.Scheme.isIso_over_nonvanishingOpen X N b
  exact tensorSection_regularTensorQuotientOnOpen X L N b _ _

end AlgebraicGeometry.Scheme.Modules

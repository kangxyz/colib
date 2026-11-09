/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionUnitNaturality

/-! Nontrivial-variable consumers of the actual section action and both evaluation routes. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.RegularSequence (globalSmulCenter)

noncomputable section

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt boundedAboveFlatPerfectGlobalUnitIso
  boundedAboveFlatAffineSectionsMap boundedAboveFlatAffineSectionUnitIso
universe u

variable (R : CommRingCat.{u}) (q : (Γ(Spec R, ⊤))ˣ)
  (s : BoundedAboveFlatAffineSections R) (j : Under R) (n : ℤ)

example :
    ((boundedAboveFlatPerfectComplex (Spec j.right).toRingedSpace).ι.map
      ((boundedAboveFlatAffineEvaluationAt R j).map
        ((boundedAboveFlatAffineSectionUnitIso R q).inv.app s))).f n =
      (globalSmulCenter (Spec j.right) ((Spec.map j.hom).appTop (↑(q⁻¹) : Γ(Spec R, ⊤)))).app
        (((boundedAboveFlatAffineEvaluationAt R j).obj s).obj.X n) := by
  let K := (boundedAboveFlatAffineEvaluationAt R j).obj s
  let q' : (Γ(Spec j.right, ⊤))ˣ :=
    Units.map (Spec.map j.hom).appTop.hom.toMonoidHom q
  have h := boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_inv R q s j
  have ht := congrArg
    (fun φ : K ⟶ K =>
      ((boundedAboveFlatPerfectComplex (Spec j.right).toRingedSpace).ι.map φ).f n) h
  have hs : (↑(q'⁻¹) : Γ(Spec j.right, ⊤)) = (Spec.map j.hom).appTop (↑(q⁻¹) : Γ(Spec R, ⊤)) :=
    Units.coe_map_inv (Spec.map j.hom).appTop.hom.toMonoidHom q
  exact (ht.trans
    (boundedAboveFlatPerfectGlobalUnitIso_inv_terms (Spec j.right) q' K n)).trans
      (congrArg (fun a : Γ(Spec j.right, ⊤) =>
        (globalSmulCenter (Spec j.right) a).app (K.obj.X n)) hs)


/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCylinderSheafHomotopy

import Mathlib.CategoryTheory.HomCongr

/-!
# Parameter cylinders on reduced hypercohomology

The native comparison with morphisms into a K-injective complex carries the
same cylinder projection through localization. It gives a criterion for the
original reduced hypercohomology in terms of the underlying projection map
on an actual K-injective model of the coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe d w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v w}]
  [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{max v w})]

variable (K : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) (p : ℤ)
  (I : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) [I.IsKInjective]
  (e : DerivedCategory.Q.obj I ≅ (DerivedCategory.Q.obj K)⟦p⟧)

/-- Homotopy classes with a K-injective model compute the original reduced hypercohomology. -/
@[no_expose]
def kInjectiveReducedHypercohomologyEquiv (X : PointedSimplicialPresheaf.{max v w} C) :
    let H := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{max v w}) (.up ℤ)
    (H.obj ((reducedCochains C J).obj X) ⟶ H.obj I) ≃
      (reducedHypercohomology C J K p).obj (op X) := by
  let A := Sheaf J AddCommGrpCat.{max v w}
  let H := HomotopyCategory.quotient A (.up ℤ)
  let a := DerivedCategory.quotientCompQhIso A
  exact (Equiv.ofBijective _
    (CochainComplex.IsKInjective.Qh_map_bijective (H.obj ((reducedCochains C J).obj X)) I)).trans
    ((a.app ((reducedCochains C J).obj X)).homCongr ((a.app I) ≪≫ e))

set_option maxHeartbeats 600000 in
-- Checking the comparison unfolds the quotient and derived functors at independent universes.
set_option backward.isDefEq.respectTransparency false in
/-- Localization of the original pointed map acts by the original reduced restriction. -/
theorem kInjectiveReducedHypercohomologyEquiv_precomp
    {X Y : PointedSimplicialPresheaf.{max v w} C} (f : X ⟶ Y)
    (g : (HomotopyCategory.quotient _ (.up ℤ)).obj ((reducedCochains C J).obj Y) ⟶
      (HomotopyCategory.quotient _ (.up ℤ)).obj I) :
    kInjectiveReducedHypercohomologyEquiv C J K p I e X
        ((HomotopyCategory.quotient _ (.up ℤ)).map ((reducedCochains C J).map f) ≫ g) =
      (reducedHypercohomology C J K p).map f.op
        (kInjectiveReducedHypercohomologyEquiv C J K p I e Y g) := by
  let A := Sheaf J AddCommGrpCat.{max v w}
  let H := HomotopyCategory.quotient A (.up ℤ)
  let Q : _ ⥤ DerivedCategory.{d} A := DerivedCategory.Q
  let Qh : _ ⥤ DerivedCategory.{d} A := DerivedCategory.Qh
  let a := DerivedCategory.quotientCompQhIso A
  let R := reducedCochains.{max v w} C J
  change a.inv.app (R.obj X) ≫ Qh.map (H.map (R.map f) ≫ g) ≫ a.hom.app I ≫ e.hom =
    Q.map (R.map f) ≫ a.inv.app (R.obj Y) ≫ Qh.map g ≫ a.hom.app I ≫ e.hom
  rw [Qh.map_comp]
  have hn : Q.map (R.map f) ≫ a.inv.app (R.obj Y) =
      a.inv.app (R.obj X) ≫ Qh.map (H.map (R.map f)) := a.inv.naturality (R.map f)
  simpa only [Category.assoc] using
    (congrArg (fun t ↦ t ≫ Qh.map g ≫ a.hom.app I ≫ e.hom) hn).symm

variable [HasBinaryProducts C] (V : C)

include e in
set_option backward.isDefEq.respectTransparency false in
/-- Quasi-isomorphic projection pullback on a K-injective coefficient model
gives invariance of the actual reduced hypercohomology on every pointed cylinder. -/
theorem bijective_reducedHypercohomology_map_cylinder_of_kInjective
    (hI : QuasiIso ((ParameterCoproduct.homologicalProjectionPullback V AddCommGrpCat.{max v w}
      (.up ℤ)).app (((sheafToPresheaf J AddCommGrpCat.{max v w}).mapHomologicalComplex
        (.up ℤ)).obj I)))
    (X : PointedSimplicialPresheaf.{max v w} C) :
    Function.Bijective ((reducedHypercohomology C J K p).map
      (cylinderProjection X (liftedRepresentableInterval V)).op) := by
  let H := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{max v w}) (.up ℤ)
  let R := reducedCochains.{max v w} C J
  let Y := parameterizedCylinder X (liftedRepresentableInterval V)
  let f : Y ⟶ X := cylinderProjection X (liftedRepresentableInterval V)
  let F := reducedHypercohomology C J K p
  let E (Z : PointedSimplicialPresheaf.{max v w} C) :=
    kInjectiveReducedHypercohomologyEquiv C J K p I e Z
  have h := bijective_precomp_reducedCochains_cylinder C J V I hI X
  have hf : (F.map f.op : F.obj (op X) → F.obj (op Y)) =
      (E Y) ∘ (fun g : H.obj (R.obj X) ⟶ H.obj I ↦ H.map (R.map f) ≫ g) ∘ (E X).symm := by
    funext z
    change F.map f.op z = E Y (H.map (R.map f) ≫ (E X).symm z)
    rw [kInjectiveReducedHypercohomologyEquiv_precomp, Equiv.apply_symm_apply]
  change Function.Bijective (F.map f.op)
  rw [hf]
  exact (E Y).bijective.comp (h.comp (E X).symm.bijective)

end CategoryTheory.PointedSimplicialPresheaf

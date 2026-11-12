/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.OrdinaryComparison
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Whole-cylinder effacement by an original marked base refinement

The witness is an arrow of the unchanged native point category. In the
degree-induction application, this result is used only in a previously proved
positive degree for the contraction coefficient. It does not supply homotopy
invariance in the degree currently being proved.
-/


/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Cylinder/LocalEffacement.lean`, blob
`c9fd4621ae67dce2ae3ac82b3063aeaf86970fd0`.
Only actual zero restriction and colimit representatives are transported here.
The original lower-degree HI-to-higher-image argument is not assumed or imported.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE

/-- An actual small-site zero restriction on the literal projection base
change kills the original big-site cylinder germ. The existing natural
comparison transports through `a1BaseChangeIso`; the two test objects are not
treated as definitionally equal. -/
theorem pointedCylinder_germ_eq_zero_of_ordinary_base_refinement
    (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
    (Φ : (nisnevichTopology X.left).Point.{u + 1})
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X).left)
        AddCommGrpCat.{u + 1})]
    (n : ℕ) {V W : Φ.fiber.Elements} (a : W ⟶ V)
    (s : (pointedCylinderValues R (X := X) Φ
      (cohomologyPresheaf.{u + 1, u + 1} F n)
      (pointedBase R (X := X) Φ)).obj (op V))
    (hz : (ordinaryPointCohomologyDiagram
      ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app X).left Φ
      (F := (restrict (SmoothSite.Contraction.affineLineCylinder.obj X)
        AddCommGrpCat.{u + 1}).obj F) n).map a.op
        ((pointedCylinderOrdinaryIso R X Φ F n).hom.app (op V) s) = 0) :
    colimit.ι (pointedCylinderValues R (X := X) Φ
      (cohomologyPresheaf.{u + 1, u + 1} F n)
      (pointedBase R (X := X) Φ)) (op V) s = 0 := by
  let D := pointedCylinderValues R (X := X) Φ
    (cohomologyPresheaf.{u + 1, u + 1} F n) (pointedBase R (X := X) Φ)
  let e := pointedCylinderOrdinaryIso R X Φ F n
  have hzero : D.map a.op s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app (op W))).1
    rw [map_zero]
    have h := ConcreteCategory.congr_hom (e.hom.naturality a.op) s
    change (e.hom.app (op W)) (D.map a.op s) = _ at h
    exact h.trans hz
  have h := ConcreteCategory.congr_hom (colimit.w D a.op) s
  simpa only [ConcreteCategory.comp_apply, hzero, map_zero] using h.symm

/-- A zero original cylinder germ is witnessed by a genuine refinement of the
marked BASE, not by an arbitrary etale neighborhood of its cylinder. -/
theorem exists_pointed_cylinder_restriction_zero_of_colimit_isZero
    (R : CommRingCat.{u}) {X : SmoothSite (Spec R)}
    (Φ : (nisnevichTopology X.left).Point.{u + 1})
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hzero : IsZero (colimit
      (pointedCylinderValues R (X := X) Φ P (pointedBase R (X := X) Φ))))
    (V : Φ.fiber.Elements)
    (s : (pointedCylinderValues R (X := X) Φ P (pointedBase R (X := X) Φ)).obj (op V)) :
    ∃ (W : Φ.fiber.Elements) (a : W ⟶ V),
      P.map (SmoothSite.Contraction.affineLineCylinder.map
        ((pointedBase R (X := X) Φ).map a)).op s = 0 := by
  let D := pointedCylinderValues R (X := X) Φ P (pointedBase R (X := X) Φ)
  have hsub : Subsingleton ↑(colimit D) := AddCommGrpCat.subsingleton_of_isZero hzero
  have he : colimit.ι D (op V) s = colimit.ι D (op V) 0 :=
    @Subsingleton.elim ↑(colimit D) hsub _ _
  obtain ⟨W, a, ha⟩ := ((colimit.isColimit D).eq_iff' s 0).mp he
  refine ⟨W.unop, a.unop, ?_⟩
  change D.map a s = 0
  simpa only [map_zero] using ha

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

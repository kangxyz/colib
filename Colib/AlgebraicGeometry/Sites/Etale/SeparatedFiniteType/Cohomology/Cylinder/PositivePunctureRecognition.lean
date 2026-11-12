/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.EdgeWindow
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.OrdinaryComparison
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1PunctureBaseChange

/-!
# The marked cylinder puncture kernel in positive degrees

The genuine open edge is injective when the required lower right-derived
image window vanishes. The actual puncture base change then identifies
the original marked restriction kernel with the coefficient kernel.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Cylinder/PositiveRestriction.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `af497b2afa790c83460569c4ccdb7fcc068a3edb`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

/-- An ordinary restriction zero gives a coefficient kernel equation when
the original higher open-image window vanishes below the specified degree. -/
theorem coefficient_kernel_of_original_restriction_zero
    {B : Scheme.{u}} [IsAffine B] {Y U : SmoothSite B} (j : U ⟶ Y)
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (nisnevichTopology U.left) AddCommGrpCat.{u + 1})]
    (n : ℕ) (V : EtaleSeparatedFiniteType Y.left)
    (hwindow : ∀ m : ℕ, 0 < m → m < n →
      IsZero (((directImage j.left).rightDerived m).obj
        ((restrict U AddCommGrpCat).obj F)))
    (x : (cohomologyPresheaf.{u + 1, u + 1} F n).obj (op ((toSmoothSite Y).obj V)))
    (hx : (cohomologyPresheaf.{u + 1, u + 1} F n).map
      ((restrictionProjection j).app V).op x = 0) :
    (cohomologyRestrictionEquiv Y F n V x).comp
      (Ext.mk₀ (restrictionToDirectImage F j)) (add_zero n) = 0 := by
  apply ordinaryEdgeMap_injective_of_rightDerived_window j.left V
    ((restrict U AddCommGrpCat).obj F) n hwindow
  rw [map_zero]
  have he := ordinaryEdgeMap_restrictionToDirectImage j F n V x
  rw [hx, map_zero] at he
  exact he

/-- The original marked-cylinder puncture-zero representative has zero image
under the actual coefficient restriction after the genuine base-change comparison. -/
theorem pointedCylinder_coefficient_kernel_of_puncture_restriction_zero
    (R : CommRingCat.{u}) {E U : SmoothSite (Spec R)} (j : U ⟶ E)
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj E).left)
        AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj U).left)
        AddCommGrpCat.{u + 1})]
    (n : ℕ) (Φ : (nisnevichTopology E.left).Point.{u + 1}) (V : Φ.fiber.Elements)
    (hwindow : ∀ m : ℕ, 0 < m → m < n →
      IsZero (((directImage (SmoothSite.Contraction.affineLineCylinder.map j).left).rightDerived
        m).obj ((restrict (SmoothSite.Contraction.affineLineCylinder.obj U) AddCommGrpCat).obj F)))
    (s : (pointedCylinderValues R (X := E) Φ (cohomologyPresheaf.{u + 1, u + 1} F n)
      (pointedBase R (X := E) Φ)).obj (op V))
    (hs : (pointedCylinderRestriction R j Φ
      (cohomologyPresheaf.{u + 1, u + 1} F n)).app (op V) s = 0) :
    ((pointedCylinderOrdinaryIso R E Φ F n).hom.app (op V) s).comp
      (Ext.mk₀ (restrictionToDirectImage F
        (SmoothSite.Contraction.affineLineCylinder.map j))) (add_zero n) = 0 := by
  let P := cohomologyPresheaf.{u + 1, u + 1} F n
  let π := (SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E
  let j₁ := SmoothSite.Contraction.affineLineCylinder.map j
  let V₁ := (baseChange π.left).obj V.obj
  let t := P.map (a1BaseChangeIso R E V.obj).hom.op s
  have ht : P.map ((restrictionProjection j₁).app V₁).op t = 0 := by
    change P.map ((restrictionProjection j₁).app V₁).op
      (P.map (a1BaseChangeIso R E V.obj).hom.op s) = 0
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      a1PunctureProjectionBaseChangeIso_restriction]
    change P.map (SmoothSite.Contraction.affineLineCylinder.map
      ((restrictionProjection j).app V.obj)).op s = 0 at hs
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    erw [hs]
    simp only [map_zero]
  exact coefficient_kernel_of_original_restriction_zero j₁ F n V₁ hwindow t ht

/-- Actual local kernel zero on the marked base implies monicity of the
original cylinder-to-puncture colimit map. -/
theorem pointedCylinderRestriction_colimit_mono_of_local_kernel
    (R : CommRingCat.{u}) {E U : SmoothSite (Spec R)} (j : U ⟶ E)
    (Φ : (nisnevichTopology E.left).Point.{u + 1})
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hzero : ∀ (V : Φ.fiber.Elements)
      (s : (pointedCylinderValues R (X := E) Φ P (pointedBase R (X := E) Φ)).obj (op V)),
      (pointedCylinderRestriction R j Φ P).app (op V) s = 0 →
        colimit.ι (pointedCylinderValues R (X := E) Φ P (pointedBase R (X := E) Φ)) (op V) s = 0) :
    Mono (colim.map (pointedCylinderRestriction R j Φ P)) := by
  let D := pointedCylinderValues R (X := E) Φ P (pointedBase R (X := E) Φ)
  let T := pointedCylinderValues R (X := E) Φ P (pointedPuncture R j Φ)
  let r := pointedCylinderRestriction R j Φ P
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨V, v, s, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := (toSmoothSite E ⋙ SmoothSite.Contraction.affineLineCylinder).op ⋙ P) z
  let N : Φ.fiber.Elements := Functor.elementsMk _ V v
  have he : colimit.ι T (op N) (r.app (op N) s) = colimit.ι T (op N) 0 := by
    rw [map_zero]
    have h := ConcreteCategory.congr_hom (colimit.ι_map r (op N)) s
    exact h.symm.trans hz
  obtain ⟨W, a, ha⟩ := ((colimit.isColimit T).eq_iff' (r.app (op N) s) 0).mp he
  have hlocal : r.app W (D.map a s) = 0 := by
    rw [NatTrans.naturality_apply]
    simpa only [map_zero] using ha
  have hw := ConcreteCategory.congr_hom (colimit.w D a) s
  exact hw.symm.trans (hzero W.unop (D.map a s) hlocal)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.SectionModelRefinement
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic

/-! # The same original model under a composite stage refinement

The native canonical pullback cocycle identifies repeated original-model refinements
with the direct refinement. Original section recovery is transported by the actual
stage comparison, without choosing a replacement original model.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem refine_comp_aux {C : Type*} [Category C] {M A B D E : C}
    (e : M ≅ E) (a : A ≅ B) (b : B ≅ E) (c : A ≅ D) (d : D ≅ E)
    (h : a ≪≫ b = c ≪≫ d) : e ≪≫ b.symm ≪≫ a.symm ≪≫ c = e ≪≫ d.symm := by
  have H := congrArg (fun z => z.symm) h
  simp only [Iso.trans_symm] at H
  rw [← Iso.trans_assoc b.symm a.symm c, H]
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- Repeated refinement of the specified original module model agrees with its
direct refinement after the actual canonical stage comparison. -/
theorem refinedSectionModelIso_comp {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (p : W ⟶ Y) (r : X ⟶ Z) (q : W ⟶ Z)
    (hfg : f ≫ g = p) (hgh : g ≫ h = r) (hph : p ≫ h = q) (hfr : f ≫ r = q)
    (L : Z.Modules) {M : W.Modules} (E : M ≅ (pullback q).obj L) :
    refinedSectionModelIso f g p hfg ((pullback h).obj L)
        (refinedSectionModelIso p h q hph L E) ≪≫
        (pullback f).mapIso (canIso g h r hgh L) =
      refinedSectionModelIso f r q hfr L E := by
  simp only [refinedSectionModelIso, Iso.trans_assoc]
  apply refine_comp_aux E
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, canIso_hom]
  exact (canHom_comp f g h p r q hfg hgh hph hfr L).symm

/-- The actual section under repeated refinement recovers the same original
section under the direct model and canonical stage-section comparison. -/
theorem refinedSectionModelIso_comp_section {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (p : W ⟶ Y) (r : X ⟶ Z) (q : W ⟶ Z)
    (hfg : f ≫ g = p) (hgh : g ≫ h = r) (hph : p ≫ h = q) (hfr : f ≫ r = q)
    (L : Z.Modules) {M : W.Modules} (E : M ≅ (pullback q).obj L)
    (s : Γ(M, ⊤)) (t : Γ((pullback g).obj ((pullback h).obj L), ⊤))
    (ht : Hom.app
      (refinedSectionModelIso f g p hfg ((pullback h).obj L)
        (refinedSectionModelIso p h q hph L E)).hom ⊤ s = pullbackGlobalSections f _ t) :
    Hom.app (refinedSectionModelIso f r q hfr L E).hom ⊤ s =
      pullbackGlobalSections f _ (Hom.app (canIso g h r hgh L).hom ⊤ t) := by
  have H := congrArg (fun e => Hom.app (Iso.hom e) ⊤ s)
    (refinedSectionModelIso_comp f g h p r q hfg hgh hph hfr L E)
  refine H.symm.trans ?_
  change Hom.app ((pullback f).map (canIso g h r hgh L).hom) ⊤
    (Hom.app (refinedSectionModelIso f g p hfg ((pullback h).obj L)
      (refinedSectionModelIso p h q hph L E)).hom ⊤ s) = _
  exact (congrArg (Hom.app ((pullback f).map (canIso g h r hgh L).hom) ⊤) ht).trans
    (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
      f (canIso g h r hgh L).hom t).symm

end AlgebraicGeometry.Scheme.Modules

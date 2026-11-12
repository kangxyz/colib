/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic

/-! # Final numerator normalization with the original bundles and frames -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- Normalize only the section's tensor comparison, without changing either bundle
or either prescribed boundary frame. Applied with c=pullbackTensorIso (C.map h) Mj' Nj,
this turns the original existential's last numerator equation into the consumer's
literal boundary-one equation for aFinal := c.hom.app top (h* a). -/
theorem original_auxiliary_numerator_final_one
    {B X : Scheme.{u}} (i : B ⟶ X) (Q R : X.Modules) (c : Q ≅ R)
    (t : (Scheme.Modules.pullback i).obj R ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(Q, ⊤))
    (ha : Hom.app ((Scheme.Modules.pullback i).mapIso c ≪≫ t).hom ⊤
      (pullbackGlobalSections i Q a) = (1 : Γ(B, ⊤))) :
    Hom.app t.hom ⊤ (pullbackGlobalSections i R (Hom.app c.hom ⊤ a)) =
      (1 : Γ(B, ⊤)) := by
  have hn := Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
    i c.hom a
  change Hom.app t.hom ⊤
    (Hom.app ((Scheme.Modules.pullback i).map c.hom) ⊤
      (pullbackGlobalSections i Q a)) = (1 : Γ(B, ⊤)) at ha
  exact (congrArg (Hom.app t.hom ⊤) hn).trans ha

end Stacks.AlgebraicGeometry.ModuleLimits

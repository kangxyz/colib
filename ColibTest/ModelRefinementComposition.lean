/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.ModelRefinementComposition

/-! # Direct and iterated models retain the same original section -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules

example {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (p : W ⟶ Y) (r : X ⟶ Z) (q : W ⟶ Z)
    (hfg : f ≫ g = p) (hgh : g ≫ h = r) (hph : p ≫ h = q) (hfr : f ≫ r = q)
    (L : Z.Modules) {M : W.Modules} (E : M ≅ (pullback q).obj L) :
    refinedSectionModelIso f g p hfg ((pullback h).obj L)
        (refinedSectionModelIso p h q hph L E) ≪≫
        (pullback f).mapIso (canIso g h r hgh L) =
      refinedSectionModelIso f r q hfr L E := refinedSectionModelIso_comp f g h p r q hfg hgh hph hfr L E

#print axioms refinedSectionModelIso_comp

example {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (p : W ⟶ Y) (r : X ⟶ Z) (q : W ⟶ Z)
    (hfg : f ≫ g = p) (hgh : g ≫ h = r) (hph : p ≫ h = q) (hfr : f ≫ r = q)
    (L : Z.Modules) {M : W.Modules} (E : M ≅ (pullback q).obj L)
    (s : Γ(M, ⊤)) (t : Γ((pullback g).obj ((pullback h).obj L), ⊤))
    (ht : Hom.app
      (refinedSectionModelIso f g p hfg ((pullback h).obj L)
        (refinedSectionModelIso p h q hph L E)).hom ⊤ s = pullbackGlobalSections f _ t) :
    Hom.app (refinedSectionModelIso f r q hfr L E).hom ⊤ s =
      pullbackGlobalSections f _ (Hom.app (canIso g h r hgh L).hom ⊤ t) := refinedSectionModelIso_comp_section f g h p r q hfg hgh hph hfr L E s t ht

#print axioms refinedSectionModelIso_comp_section

end AlgebraicGeometry.Scheme.Modules

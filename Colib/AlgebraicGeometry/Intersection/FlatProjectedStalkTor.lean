/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.FlatProjectionStalkTor
public import StacksFrontier.Homology.Tor.Presentation

/-!
# Positive actual stalk Tor for a flat projected first map

Removing the actual flat ambient projection leaves the original first support
stalk flat over the original base stalk. Native flat-module Tor acyclicity then
applies, with the original left/right order and every point transport retained.
No flatness is required of the second closed support.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {T X C : Scheme.{u}} (p : T ⟶ X) (i : C ⟶ T) (I : X.IdealSheafData)
  [Flat p] [Flat (i ≫ p)]

/-- Actual projected flatness makes positive pulled-support Tor vanish. -/
theorem isZero_torStalkComap_succ_of_flat_composite
    (c : C) (d : (I.comap p).subscheme) (e : I.subscheme)
    (hd : i c = (I.comap p).subschemeι d) (he : p (i c) = I.subschemeι e) (n : ℕ) :
    IsZero ((((Tor (ModuleCat (T.presheaf.stalk (i c))) (n + 1)).obj
      ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
          (I.comap p).subschemeι.stalkMap d).hom).obj
        (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
          ((I.comap p).subscheme.presheaf.stalk d))))) := by
  apply isZero_torStalkComap_of_flatProjection p I i c d e hd he (n + 1)
  let M := (ModuleCat.restrictScalars ((i ≫ p).stalkMap c).hom).obj
    (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c))
  haveI : Module.Flat (X.presheaf.stalk ((i ≫ p) c)) M := Flat.stalkMap (i ≫ p) c
  exact isZero_Tor_succ_of_flat M _ n

/-- The same comparison at a separately named actual ambient incidence point. -/
theorem isZero_torStalkComap_succ_of_flat_composite_of_eq
    (c : C) (t : T) (d : (I.comap p).subscheme) (e : I.subscheme)
    (hc : t = i c) (hd : t = (I.comap p).subschemeι d)
    (he : p t = I.subschemeι e) (n : ℕ) :
    IsZero ((((Tor (ModuleCat (T.presheaf.stalk t)) (n + 1)).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hc)).hom ≫ i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
          (I.comap p).subschemeι.stalkMap d).hom).obj
        (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
          ((I.comap p).subscheme.presheaf.stalk d))))) := by
  subst t
  simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] using
      isZero_torStalkComap_succ_of_flat_composite p i I c d e hd he n

end AlgebraicGeometry.Scheme.Hom

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.AmbientTorPointTransport

/-!
# Native pair-point transport consumer

The support point is the actual image of an incidence
point; the triple scalar map is the actual stalk map preceded by the inverse
ambient point cast. No comparison, vanishing or regularity is supplied.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u
variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (x : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "A" => correspondenceIntersectionAmbient f g h
local notation3 (prettyPrint := false) "P" => correspondenceSupportProduct f g h z w
local notation3 (prettyPrint := false) "i" => correspondenceSupportProductInclusion f g h z w
local notation3 (prettyPrint := false) "b" => correspondenceIncidenceToSupportProduct f g h z w
local notation3 (prettyPrint := false) "v" => correspondenceIncidenceInclusion f g h z w
local notation3 (prettyPrint := false) "L" =>
  (correspondenceTripleProduct f g h).presheaf.stalk (v x)
local notation3 (prettyPrint := false) "e" =>
  correspondenceIncidenceAmbientStalkIsoOfSupportPoint f g h z w x (b x) rfl
local notation3 (prettyPrint := false) "χ" =>
  ((correspondenceTripleInclusion f g h).stalkMap (v x)).hom.comp (e).inv.hom

example (n : ℕ) :
    Nonempty (correspondenceIncidenceAmbientTor f g h z w x n ≅
      (ModuleCat.restrictScalars (e).hom.hom).obj
        (((Tor (ModuleCat ((A).presheaf.stalk (i (b x)))) n).obj
          ((ModuleCat.restrictScalars ((i).stalkMap (b x)).hom).obj
            (ModuleCat.of ((P).presheaf.stalk (b x)) ((P).presheaf.stalk (b x))))).obj
              ((ModuleCat.restrictScalars χ).obj (ModuleCat.of L L)))) := by
  refine ⟨correspondenceIncidenceAmbientTorIsoOfSupportPoint f g h z w x
    (b x) rfl χ ?_ n⟩
  exact (congrArg CommRingCat.Hom.hom
    (show (e).hom ≫ ((e).inv ≫ (correspondenceTripleInclusion f g h).stalkMap (v x)) =
      (correspondenceTripleInclusion f g h).stalkMap (v x) by simp)).symm

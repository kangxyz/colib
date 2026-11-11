/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.PairTorAction
public import StacksFrontier.Homology.Tor.Independence

/-!
# Ambient Tor at an equal actual support point

The native pair Tor orders its factors as support, triple.
An equality of support points gives an explicit structure-sheaf stalk isomorphism
from the native ambient stalk to the ambient stalk over the chosen support point.
The triple scalar map is retained through its displayed equality after this cast.

The comparison uses the public ring-equivalence restriction theorem
`RingTheory.TorIndependence.torRestrictIso`; it does not rebuild resolutions or
claim coefficient-ring linearity. No regular list, vanishing, quotient equivalence,
or Tor comparison is accepted as an input. Every degree, including zero, is allowed.

Software providers: Colib e7697ab8164435c7093665d02ac34f021eefb75e,
`Composition/StalkModules.lean:46-82` and `Composition/PairTorAction.lean:46-56`;
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
`Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:248-254`;
Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7,
`StacksFrontier/Homology/Tor/Independence.lean:155-169`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
namespace Stacks.Chow

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

/-- The actual equality cast from the native ambient stalk to the ambient over `d`. -/
def correspondenceIncidenceAmbientStalkIsoOfSupportPoint (d : P) (hd : d = b x) :
    correspondenceIncidenceAmbientStalk f g h z w x ≅ (A).presheaf.stalk (i d) :=
  (A).presheaf.stalkCongr (.of_eq
    ((correspondenceIncidence_ambient_point_eq f g h z w x).trans (congrArg i hd.symm)))

/-- The support module transport retains its literal native scalar map. -/
theorem correspondenceIncidenceAmbientStalkIsoOfSupportPoint_support
    (d : P) (hd : d = b x) :
    (correspondenceIncidenceAmbientStalkIsoOfSupportPoint f g h z w x d hd).hom ≫
        (i).stalkMap d ≫ ((P).presheaf.stalkCongr (.of_eq hd)).hom =
      ((A).presheaf.stalkCongr
        (.of_eq (correspondenceIncidence_ambient_point_eq f g h z w x))).hom ≫
          (i).stalkMap (b x) := by
  subst d
  simp only [correspondenceIncidenceAmbientStalkIsoOfSupportPoint,
    TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.comp_id]

/-- Native pair Tor at an equal support point, with the triple scalar map explicitly matched.
The result is linear over the native ambient stalk, by restriction along the named point cast. -/
def correspondenceIncidenceAmbientTorIsoOfSupportPoint (d : P) (hd : d = b x)
    (χ : (A).presheaf.stalk (i d) →+* L)
    (hχ : ((correspondenceTripleInclusion f g h).stalkMap (v x)).hom =
      χ.comp (correspondenceIncidenceAmbientStalkIsoOfSupportPoint
        f g h z w x d hd).hom.hom) (n : ℕ) :
    correspondenceIncidenceAmbientTor f g h z w x n ≅
      (ModuleCat.restrictScalars (correspondenceIncidenceAmbientStalkIsoOfSupportPoint
        f g h z w x d hd).hom.hom).obj
        (((Tor (ModuleCat ((A).presheaf.stalk (i d))) n).obj
          ((ModuleCat.restrictScalars ((i).stalkMap d).hom).obj
            (ModuleCat.of ((P).presheaf.stalk d) ((P).presheaf.stalk d)))).obj
              ((ModuleCat.restrictScalars χ).obj (ModuleCat.of L L))) := by
  subst d
  let e := correspondenceIncidenceAmbientStalkIsoOfSupportPoint f g h z w x (b x) rfl
  let eR := e.commRingCatIsoToRingEquiv
  let M := (ModuleCat.restrictScalars ((i).stalkMap (b x)).hom).obj
    (ModuleCat.of ((P).presheaf.stalk (b x)) ((P).presheaf.stalk (b x)))
  let N := (ModuleCat.restrictScalars χ).obj (ModuleCat.of L L)
  let eM : correspondenceIncidenceSupportStalkModule f g h z w x ≅
      (ModuleCat.restrictScalars eR.toRingHom).obj M :=
    ModuleCat.restrictScalarsComp'App eR.toRingHom ((i).stalkMap (b x)).hom
      ((((A).presheaf.stalkCongr
        (.of_eq (correspondenceIncidence_ambient_point_eq f g h z w x))).hom ≫
          (i).stalkMap (b x)).hom) rfl
      (ModuleCat.of ((P).presheaf.stalk (b x)) ((P).presheaf.stalk (b x)))
  let eN : correspondenceIncidenceTripleStalkModule f g h z w x ≅
      (ModuleCat.restrictScalars eR.toRingHom).obj N :=
    ModuleCat.restrictScalarsComp'App eR.toRingHom χ
      ((correspondenceTripleInclusion f g h).stalkMap (v x)).hom hχ
      (ModuleCat.of L L)
  exact (((Tor
      (ModuleCat (correspondenceIncidenceAmbientStalk f g h z w x)) n).mapIso eM).app
      (correspondenceIncidenceTripleStalkModule f g h z w x)) ≪≫
    ((Tor (ModuleCat (correspondenceIncidenceAmbientStalk f g h z w x)) n).obj
      ((ModuleCat.restrictScalars eR.toRingHom).obj M)).mapIso eN ≪≫
    RingTheory.TorIndependence.torRestrictIso eR M N n

end Stacks.Chow

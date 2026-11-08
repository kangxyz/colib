/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.StalkModules
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafMultiplicity

/-!
# Actual structure-ring stalks in the incidence Tor coefficients

New source reconstruction after executor replacement. This is not asserted to
match the historical file bytes and has not been compiled in the replacement
executor. Native `StalkModules` definitions are imported, not duplicated.

The stalks of the actual pushed-forward structure sheaves identify with the
actual support-product and triple-product local rings, retaining their ambient
stalk actions. Applying native categorical Tor to these actual module
isomorphisms gives the coefficient comparison. No comparison is assumed.

Native suppliers: `stalkPushforwardStructureSheafLinearEquiv` in
`StacksFrontier/AlgebraicGeometry/Chow/CoherentCycle/ClosedSubscheme.lean` and
`length_stalk_torSheaf_eq_length_tor_stalk` in
`StacksFrontier/AlgebraicGeometry/Intersection/TorFormula/TorSheafMultiplicity.lean`.
References: Stacks Project, Tags 0AZT, 02QX, 01CB, 00M1. Original orientation:
motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/AlgebraicGeometry/Intersection/StalkModules.lean` and actual
correspondence `Composition/Incidence/GenericTor.lean`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- A structure-sheaf stalk at an equal ambient image, with the exact transported action. -/
def stalkPushforwardStructureSheafIsoOfEq {P W : Scheme.{u}} (j : W ⟶ P) (w : W)
    (x : P) (hx : x = j w)
    (hj : Topology.IsInducing (ConcreteCategory.hom j.base)) :
    TorFormula.stalkModuleCat P ((Scheme.Modules.pushforward j).obj (Ample.unitModule W)) x ≅
      (ModuleCat.restrictScalars
        ((P.presheaf.stalkCongr (.of_eq hx)).hom ≫ j.stalkMap w).hom).obj
        (ModuleCat.of (W.presheaf.stalk w) (W.presheaf.stalk w)) := by
  subst x
  have heq : ((P.presheaf.stalkCongr (.of_eq (rfl : j w = j w))).hom ≫
      j.stalkMap w).hom = (j.stalkMap w).hom := by simp
  exact (stalkPushforwardStructureSheafLinearEquiv j w hj).toModuleIso ≪≫
    (ModuleCat.restrictScalarsCongr heq.symm).app
      (ModuleCat.of (W.presheaf.stalk w) (W.presheaf.stalk w))

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The product-support structure sheaf has its actual local structure ring as stalk. -/
def incidenceSupportStructureStalkIso (t : correspondenceIncidence f g h z w) :
    TorFormula.stalkModuleCat (correspondenceIntersectionAmbient f g h)
      ((Scheme.Modules.pushforward (correspondenceSupportProductInclusion f g h z w)).obj
        (Ample.unitModule (correspondenceSupportProduct f g h z w)))
      (correspondenceIncidenceAmbientInclusion f g h z w t) ≅
      correspondenceIncidenceSupportStalkModule f g h z w t :=
  stalkPushforwardStructureSheafIsoOfEq
    (correspondenceSupportProductInclusion f g h z w)
    (correspondenceIncidenceToSupportProduct f g h z w t)
    (correspondenceIncidenceAmbientInclusion f g h z w t)
    (correspondenceIncidence_ambient_point_eq f g h z w t)
    (IsClosedImmersion.isClosedEmbedding
      (correspondenceSupportProductInclusion f g h z w)).isInducing

/-- The triple-product structure sheaf has its actual local structure ring as stalk. -/
def incidenceTripleStructureStalkIso [IsSeparated g]
    (t : correspondenceIncidence f g h z w) :
    TorFormula.stalkModuleCat (correspondenceIntersectionAmbient f g h)
      ((Scheme.Modules.pushforward (correspondenceTripleInclusion f g h)).obj
        (Ample.unitModule (correspondenceTripleProduct f g h)))
      (correspondenceIncidenceAmbientInclusion f g h z w t) ≅
      correspondenceIncidenceTripleStalkModule f g h z w t :=
  LinearEquiv.toModuleIso
    (stalkPushforwardStructureSheafLinearEquiv (correspondenceTripleInclusion f g h)
      (correspondenceIncidenceInclusion f g h z w t)
      (IsClosedImmersion.isClosedEmbedding (correspondenceTripleInclusion f g h)).isInducing)

/-- Actual Tor of the two sheaf stalks is Tor of the two local structure-ring modules. -/
def incidenceStructureStalkTorIso [IsSeparated g]
    (t : correspondenceIncidence f g h z w) (n : ℕ) :
    ((Tor (ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t))) n).obj
      (TorFormula.stalkModuleCat (correspondenceIntersectionAmbient f g h)
        ((Scheme.Modules.pushforward (correspondenceSupportProductInclusion f g h z w)).obj
          (Ample.unitModule (correspondenceSupportProduct f g h z w)))
        (correspondenceIncidenceAmbientInclusion f g h z w t))).obj
      (TorFormula.stalkModuleCat (correspondenceIntersectionAmbient f g h)
        ((Scheme.Modules.pushforward (correspondenceTripleInclusion f g h)).obj
          (Ample.unitModule (correspondenceTripleProduct f g h)))
        (correspondenceIncidenceAmbientInclusion f g h z w t)) ≅
    ((Tor (ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t))) n).obj
      (correspondenceIncidenceSupportStalkModule f g h z w t)).obj
      (correspondenceIncidenceTripleStalkModule f g h z w t) :=
  ((Tor _ n).mapIso (incidenceSupportStructureStalkIso f g h z w t)).app _ ≪≫
    ((Tor _ n).obj (correspondenceIncidenceSupportStalkModule f g h z w t)).mapIso
      (incidenceTripleStructureStalkIso f g h z w t)

/-- The actual Tor-sheaf stalk length equals the actual local structure-ring Tor length. -/
theorem incidenceTorSheaf_length_eq_structureStalkTor [IsSeparated g]
    (t : correspondenceIncidence f g h z w) (n : ℕ) :
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t))
      ((TorFormula.torSheaf (correspondenceIntersectionAmbient f g h)
        ((Scheme.Modules.pushforward (correspondenceSupportProductInclusion f g h z w)).obj
          (Ample.unitModule (correspondenceSupportProduct f g h z w)))
        ((Scheme.Modules.pushforward (correspondenceTripleInclusion f g h)).obj
          (Ample.unitModule (correspondenceTripleProduct f g h))) n).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t)) =
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t))
      (((Tor (ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
          (correspondenceIncidenceAmbientInclusion f g h z w t))) n).obj
        (correspondenceIncidenceSupportStalkModule f g h z w t)).obj
        (correspondenceIncidenceTripleStalkModule f g h z w t)) := by
  rw [TorFormula.length_stalk_torSheaf_eq_length_tor_stalk]
  exact (incidenceStructureStalkTorIso f g h z w t n).toLinearEquiv.length_eq

end Stacks.Chow

module

import Colib.AlgebraicGeometry.Correspondences.Composition.TorStalkComparison

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

-- New recovery tests, not the historical seven-example test file.
example {P W : Scheme.{u}} (j : W ⟶ P) (w : W) (x : P) (hx : x = j w)
    (hj : Topology.IsInducing (ConcreteCategory.hom j.base)) :
    TorFormula.stalkModuleCat P ((Scheme.Modules.pushforward j).obj (Ample.unitModule W)) x ≅
      (ModuleCat.restrictScalars
        ((P.presheaf.stalkCongr (.of_eq hx)).hom ≫ j.stalkMap w).hom).obj
        (ModuleCat.of (W.presheaf.stalk w) (W.presheaf.stalk w)) :=
  stalkPushforwardStructureSheafIsoOfEq j w x hx hj

example {P W : Scheme.{u}} (j : W ⟶ P) (w : W) [IsClosedImmersion j] :
    TorFormula.stalkModuleCat P ((Scheme.Modules.pushforward j).obj (Ample.unitModule W)) (j w) ≅
      (ModuleCat.restrictScalars (j.stalkMap w).hom).obj
        (ModuleCat.of (W.presheaf.stalk w) (W.presheaf.stalk w)) :=
  (stalkPushforwardStructureSheafLinearEquiv j w
    (IsClosedImmersion.isClosedEmbedding j).isInducing).toModuleIso

example {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsSeparated g] (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (t : correspondenceIncidence f g h z w) (n : ℕ) :
    (incidenceStructureStalkTorIso f g h z w t n).hom ≫
      (incidenceStructureStalkTorIso f g h z w t n).inv = 𝟙 _ :=
  (incidenceStructureStalkTorIso f g h z w t n).hom_inv_id

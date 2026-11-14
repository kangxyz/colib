/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.ProjectionMapLeftAdjointComparison
public import Colib.AlgebraicGeometry.EtaleCohomology.ModuleRestrictionMonoidalComparison
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModRestrictionProjectionFormula

/-!
# Native finite étale module trace projection formula

This uses the original inverse-image monoidal structure, original adjunction projection map
and original finite étale trace.
The restriction presentation is only an intermediate in the proof.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open Functor.LaxMonoidal
universe u
namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal
  etaleModuleInverseImageSheafPullbackMonoidal

set_option backward.isDefEq.respectTransparency false

variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g]

/-- The canonical native projection map, followed by the original inverse-image tensorator. -/
def finiteEtaleZModProjection (F G : EtaleModules.{u, 0} (ZMod n) X) :
    F ⊗ (etaleModuleDirectImage (ZMod n) g).obj
        ((etaleModuleInverseImage (ZMod n) g).obj G) ⟶
      (etaleModuleDirectImage (ZMod n) g).obj
        ((etaleModuleInverseImage (ZMod n) g).obj (F ⊗ G)) :=
  (etaleModuleInverseImageAdj (ZMod n) g).projectionMap F
      ((etaleModuleInverseImage (ZMod n) g).obj G) ≫
    (etaleModuleDirectImage (ZMod n) g).map
      (μ (etaleModuleInverseImage (ZMod n) g) F G)

/-- The canonical native projection map agrees with the restriction presentation under
existing left-adjoint comparison maps. -/
theorem finiteEtaleZModProjection_restriction
    (F G : EtaleModules.{u, 0} (ZMod n) X) :
    finiteEtaleZModProjection n g F G ≫
        (etaleModuleDirectImage (ZMod n) g).map
          ((etaleModuleInverseImageRestrictionIso (ZMod n) g).hom.app (F ⊗ G)) =
      (F ◁ (etaleModuleDirectImage (ZMod n) g).map
          ((etaleModuleInverseImageRestrictionIso (ZMod n) g).hom.app G)) ≫
        finiteEtaleZModRestrictionProjection n g F G := by
  have := etaleModuleInverseImageAdj_native_isMonoidal (ZMod n) g
  have := etaleModuleRestrictionDirectImageAdj_unit_isMonoidal (ZMod n) g
  exact Colib.ProjectionMap.projectionMap_leftAdjointUniq
    (etaleModuleInverseImageAdj (ZMod n) g)
    (etaleModuleRestrictionDirectImageAdj (ZMod n) g) F G

/-- The actual native finite étale trace satisfies the module tensor projection formula. -/
theorem finiteEtaleZModProjection_trace [IsFinite g]
    (F G : EtaleModules.{u, 0} (ZMod n) X) :
    finiteEtaleZModProjection n g F G ≫ finiteEtaleZModTrace n g (F ⊗ G) =
      F ◁ finiteEtaleZModTrace n g G := by
  rw [finiteEtaleZModTrace_eq_restriction n g (F ⊗ G),
    ← Category.assoc, finiteEtaleZModProjection_restriction,
    Category.assoc, finiteEtaleZModRestrictionProjection_trace,
    ← whiskerLeft_comp, ← finiteEtaleZModTrace_eq_restriction]

end Stacks.EtaleCohomology

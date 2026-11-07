/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.MappingCone
public import Colib.Topology.Prespectrum.ParameterLoopingHomotopy

/-!
# The original loop-to-cofiber comparison

Loop the entire original cone nullhomotopy and descend from the actual reduced mapping cone
of the looped arrow. This constructs the canonical map from Cone(Ωf) to ΩCone(f), retaining
the target inclusion and both independent cylinder and loop parameters. No stability or
cofiber-preservation assertion is used in this construction.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/ConeParameterLooping.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual reduced cone, complete null-cylinder, target inclusion, strict
naturality and descent through the same full nullhomotopy are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The unchanged cone cylinder is a whole nullhomotopy after parameter looping. -/
def mappingConeParameterLoopingHomotopy :
    Homotopy (parameterLoopingMap f ≫ parameterLoopingMap (mappingConeInclusion f))
      (zeroHom (parameterLooping E) (parameterLooping (mappingCone f))) :=
  (mappingConeHomotopy f).parameterLoopingNull

/-- The original reduced cone of the looped arrow maps to loops in its original reduced cone. -/
def mappingConeParameterLoopingComparison :
    mappingCone (parameterLoopingMap f) ⟶ parameterLooping (mappingCone f) :=
  mappingConeDesc (parameterLoopingMap f) (parameterLoopingMap (mappingConeInclusion f))
    (mappingConeParameterLoopingHomotopy f)

/-- The original target loop is included without reparametrization. -/
theorem mappingConeParameterLoopingComparison_inclusion :
    mappingConeInclusion (parameterLoopingMap f) ≫ mappingConeParameterLoopingComparison f =
      parameterLoopingMap (mappingConeInclusion f) :=
  mappingConeInclusion_desc _ _ _

/-- The comparison retains the entire original cylinder at each independent loop time. -/
theorem mappingConeParameterLoopingComparison_cylinder (n : ℕ) (s t : unitInterval)
    (γ : Path (E.point n) (E.point n)) :
    Path.toContinuousMap ((mappingConeParameterLoopingComparison f).map n
      (ReducedMappingCone.cylinder ((parameterLooping E).point n)
        ((parameterLooping F).point n) ((parameterLoopingMap f).map n) (s, γ))) t =
      ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, γ t) := rfl

/-- Strict arrow squares commute with the actual comparison on the target and entire cylinder. -/
theorem mappingConeParameterLoopingComparison_naturality
    {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B) :
    mappingConeMap (parameterLoopingFunctor.mapArrow.map sq) ≫
        mappingConeParameterLoopingComparison B.hom =
      mappingConeParameterLoopingComparison A.hom ≫ parameterLoopingMap (mappingConeMap sq) := by
  apply Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext
  · intro γ
    apply Path.ext
    funext t
    rfl
  · intro z
    apply Path.ext
    funext t
    rfl

/-- Descent after the comparison is descent along the pointwise loop of the same entire null track.
-/
theorem mappingConeParameterLoopingComparison_desc {G : LoopPrespectrum.{u}} (g : F ⟶ G)
    (H : Homotopy (f ≫ g) (zeroHom E G)) :
    mappingConeParameterLoopingComparison f ≫ parameterLoopingMap (mappingConeDesc f g H) =
      mappingConeDesc (parameterLoopingMap f) (parameterLoopingMap g) H.parameterLoopingNull := by
  apply Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext
  · intro γ
    apply Path.ext
    funext t
    rfl
  · intro z
    apply Path.ext
    funext t
    rfl

end Topology.LoopPrespectrum

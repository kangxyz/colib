/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.ConeParameterLooping
public import Colib.Topology.Prespectrum.FiberParameterLooping
public import Colib.Topology.Prespectrum.ConeDescStableEquivalence
public import Colib.Topology.Prespectrum.ParameterLoopingStableEquivalence

/-!
# Stable comparison of the original looped cofiber

The actual fiber lift of the looped cone nullhomotopy becomes precisely the loop of the
original cone-to-fiber map under the literal fiber-loop isomorphism. Genuine excision for
both the original arrow and its parameter-looped arrow therefore proves stability of the
unchanged Cone(Ωf) → ΩCone(f). The signed boundary equation retains the original fiber
boundary and the proved signed loop shift. Neither excision input is assumed automatically.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/ConeParameterLoopingStable.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual cone comparison and full fiber lift retain separate original and
looped excision hypotheses, all integer degrees and the existing signed boundary. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The original looped null-cylinder fiber lift is the loop of the original comparison. -/
theorem mappingConeParameterLoopingHomotopy_fiberLift :
    homotopyFiberLift (parameterLoopingMap (mappingConeInclusion f)) (parameterLoopingMap f)
        (mappingConeParameterLoopingHomotopy f) ≫
      (homotopyFiberParameterLoopingIso (mappingConeInclusion f)).hom =
        parameterLoopingMap (mappingConeFiberComparison f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

/-- The two genuine excision comparisons make the unchanged loop-to-cofiber map stable. -/
theorem mappingConeParameterLoopingComparison_isStableEquivalence
    (he : IsStableEquivalence (mappingConeFiberComparison f))
    (hΩe : IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f))) :
    IsStableEquivalence (mappingConeParameterLoopingComparison f) := by
  apply mappingConeDesc_isStableEquivalence _ _ _ hΩe
  intro d
  apply (isIso_comp_right_iff _
    ((stableHomotopyFunctor d).map
      (homotopyFiberParameterLoopingIso (mappingConeInclusion f)).hom)).mp
  rw [← Functor.map_comp, mappingConeParameterLoopingHomotopy_fiberLift]
  exact parameterLoopingMap_isStableEquivalence (mappingConeFiberComparison f) he d

/-- The same literal comparison carries the original signed cone boundary to its fiber lift. -/
theorem mappingConeParameterLoopingComparison_connecting
    (hΩe : IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f)))
    (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (mappingConeParameterLoopingComparison f) ≫
        stableFiberConnecting (parameterLoopingMap (mappingConeInclusion f)) d =
      stableMappingConeConnecting (parameterLoopingMap f) hΩe d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberLift (parameterLoopingMap (mappingConeInclusion f))
            (parameterLoopingMap f) (mappingConeParameterLoopingHomotopy f)) :=
  mappingConeDesc_connecting _ _ _ hΩe d

/-- Transport through the actual fiber-loop transpose retains the proved signed degree shift. -/
theorem mappingConeParameterLoopingComparison_connecting_shift
    (hΩe : IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f)))
    (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (mappingConeParameterLoopingComparison f) ≫
        stableFiberConnecting (parameterLoopingMap (mappingConeInclusion f)) d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberParameterLoopingIso (mappingConeInclusion f)).hom ≫
        (parameterStableHomotopyIso (homotopyFiber (mappingConeInclusion f)) d).hom =
      stableMappingConeConnecting (parameterLoopingMap f) hΩe d ≫
        (parameterStableHomotopyIso E d).hom ≫
        (stableHomotopyFunctor (d + 1)).map (mappingConeFiberComparison f) := by
  calc
    _ = ((stableHomotopyFunctor (d + 1)).map (mappingConeParameterLoopingComparison f) ≫
        stableFiberConnecting (parameterLoopingMap (mappingConeInclusion f)) d) ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberParameterLoopingIso (mappingConeInclusion f)).hom ≫
        (parameterStableHomotopyIso (homotopyFiber (mappingConeInclusion f)) d).hom := by
      simp only [Category.assoc]
    _ = (stableMappingConeConnecting (parameterLoopingMap f) hΩe d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberLift (parameterLoopingMap (mappingConeInclusion f))
            (parameterLoopingMap f) (mappingConeParameterLoopingHomotopy f))) ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberParameterLoopingIso (mappingConeInclusion f)).hom ≫
        (parameterStableHomotopyIso (homotopyFiber (mappingConeInclusion f)) d).hom := by
      rw [mappingConeParameterLoopingComparison_connecting f hΩe d]
    _ = stableMappingConeConnecting (parameterLoopingMap f) hΩe d ≫
        ((stableHomotopyFunctor d).map
          (homotopyFiberLift (parameterLoopingMap (mappingConeInclusion f))
            (parameterLoopingMap f) (mappingConeParameterLoopingHomotopy f)) ≫
          (stableHomotopyFunctor d).map
            (homotopyFiberParameterLoopingIso (mappingConeInclusion f)).hom) ≫
        (parameterStableHomotopyIso (homotopyFiber (mappingConeInclusion f)) d).hom := by
      simp only [Category.assoc]
    _ = stableMappingConeConnecting (parameterLoopingMap f) hΩe d ≫
        (stableHomotopyFunctor d).map (parameterLoopingMap (mappingConeFiberComparison f)) ≫
        (parameterStableHomotopyIso (homotopyFiber (mappingConeInclusion f)) d).hom := by
      rw [← Functor.map_comp, mappingConeParameterLoopingHomotopy_fiberLift]
    _ = _ := by rw [parameterStableHomotopyIso_naturality]

/-- A proved original cofiber descent stays stable under this literal looped descent. -/
theorem mappingConeDesc_parameterLooping_isStableEquivalence {G : LoopPrespectrum.{u}}
    (g : F ⟶ G) (H : Homotopy (f ≫ g) (zeroHom E G))
    (he : IsStableEquivalence (mappingConeFiberComparison f))
    (hΩe : IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f)))
    (hdesc : IsStableEquivalence (mappingConeDesc f g H)) :
    IsStableEquivalence
      (mappingConeDesc (parameterLoopingMap f) (parameterLoopingMap g) H.parameterLoopingNull) := by
  rw [← mappingConeParameterLoopingComparison_desc]
  exact (mappingConeParameterLoopingComparison_isStableEquivalence f he hΩe).comp
    (parameterLoopingMap_isStableEquivalence _ hdesc)

attribute [colib_tag "COL-0295"] mappingConeParameterLoopingComparison_connecting_shift

end Topology.LoopPrespectrum

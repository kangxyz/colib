/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StrictSquareConeInterchangeNaturality
public import Colib.Topology.Prespectrum.ConeParameterLoopingExcision

/-!
# The actual cofiber comparison for the original Bass square

The original cone of the looped square map maps to the original looped cone of the four
corner cofibers. The map factors the literal loop–cofiber comparison and the checked finite
cone/pushout interchange. Its target inclusion and strict cube naturality retain the original
maps. Stable preservation follows from the two genuine excision inputs, or from their proved
point-topology and linear-growth discharge. No coordinate-swap boundary sign is inferred.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare
variable {S T : Arrow (Arrow LoopPrespectrum.{u})} (a : S ⟶ T)

/-- The four literal target inclusions form the original square map into the corner cofibers. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCofiberComparison.lean:31"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
def coneSquareInclusion : T ⟶ coneSquare a :=
  Arrow.homMk
    (Arrow.homMk (f := T.left) (g := (coneSquare a).left)
      (mappingConeInclusion a.left.left) (mappingConeInclusion a.left.right)
      (by apply Hom.ext; funext n; ext x; rfl))
    (Arrow.homMk (f := T.right) (g := (coneSquare a).right)
      (mappingConeInclusion a.right.left) (mappingConeInclusion a.right.right)
      (by apply Hom.ext; funext n; ext x; rfl)) (by
        apply Arrow.hom_ext <;> apply Hom.ext <;> funext n <;> ext x <;> rfl)

/-- Compare the original cofiber of the Bass map with the Bass value of the actual corner cones. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCofiberComparison.lean:42"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
def loopedConeCofiberComparison :
    mappingCone (strictSquareLoopedConeFunctor.map a) ⟶
      strictSquareLoopedConeFunctor.obj (coneSquare a) :=
  mappingConeParameterLoopingComparison (mappingConeMap (strictSquareComparisonFunctor.map a)) ≫
    parameterLoopingMap (coneInterchangeIso a).hom

/-- The actual target inclusion is carried by the unchanged Bass image of the corner inclusions. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCofiberComparison.lean:49"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem loopedConeCofiberComparison_inclusion :
    mappingConeInclusion (strictSquareLoopedConeFunctor.map a) ≫
        loopedConeCofiberComparison a =
      strictSquareLoopedConeFunctor.map (coneSquareInclusion a) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  change Path ((mappingCone (comparison T)).point n)
    ((mappingCone (comparison T)).point n) at γ
  apply Path.ext
  funext t
  change (coneInterchangeIso a).hom.map n
      ((mappingConeInclusion (mappingConeMap (strictSquareComparisonFunctor.map a))).map n
        (γ t)) =
    (mappingConeMap (strictSquareComparisonFunctor.map (coneSquareInclusion a))).map n (γ t)
  induction γ t using Quot.inductionOn with
  | h z => cases z <;> rfl

/-- The original cofiber time and actual output-loop time remain independent. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCofiberComparison.lean:69"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem loopedConeCofiberComparison_cylinder (n : ℕ) (r t : unitInterval)
    (γ : Path ((mappingCone (comparison S)).point n) ((mappingCone (comparison S)).point n)) :
    Path.toContinuousMap ((loopedConeCofiberComparison a).map n
      (ReducedMappingCone.cylinder ((strictSquareLoopedConeFunctor.obj S).point n)
        ((strictSquareLoopedConeFunctor.obj T).point n)
        ((strictSquareLoopedConeFunctor.map a).map n) (r, γ))) t =
      (coneInterchangeIso a).hom.map n
        (ReducedMappingCone.cylinder ((mappingCone (comparison S)).point n)
          ((mappingCone (comparison T)).point n)
          ((mappingConeMap (strictSquareComparisonFunctor.map a)).map n) (r, γ t)) := rfl

/-- Actual coefficient cubes commute with the whole original cofiber comparison. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCofiberComparison.lean:81"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem loopedConeCofiberComparison_naturality
    {S' T' : Arrow (Arrow LoopPrespectrum.{u})} {b : S' ⟶ T'}
    (k : Arrow.mk a ⟶ Arrow.mk b) :
    mappingConeMap (strictSquareLoopedConeFunctor.mapArrow.map k) ≫
        loopedConeCofiberComparison b =
      loopedConeCofiberComparison a ≫ strictSquareLoopedConeFunctor.map (coneSquareMap k) := by
  apply Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext
  · intro γ
    apply Path.ext
    funext t
    exact congrArg (fun f ↦ f.map n
      ((mappingConeInclusion (mappingConeMap (strictSquareComparisonFunctor.map a))).map n
        (Path.toContinuousMap γ t))) (coneInterchangeIso_naturality k)
  · rintro ⟨r, γ⟩
    apply Path.ext
    funext t
    exact congrArg (fun f ↦ f.map n
      (ReducedMappingCone.cylinder ((mappingCone (comparison S)).point n)
        ((mappingCone (comparison T)).point n)
        ((mappingConeMap (strictSquareComparisonFunctor.map a)).map n)
        (r, Path.toContinuousMap γ t))) (coneInterchangeIso_naturality k)

/-- Two genuine original excision comparisons imply stability of the actual Bass cofiber map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCofiberComparison.lean:106"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem loopedConeCofiberComparison_isStableEquivalence
    (he : IsStableEquivalence (mappingConeFiberComparison
      (mappingConeMap (strictSquareComparisonFunctor.map a))))
    (hΩe : IsStableEquivalence (mappingConeFiberComparison
      (strictSquareLoopedConeFunctor.map a))) :
    IsStableEquivalence (loopedConeCofiberComparison a) := by
  apply (mappingConeParameterLoopingComparison_isStableEquivalence _ he hΩe).comp
  intro d
  change IsIso ((stableHomotopyFunctor d).map
    (parameterLoopingFunctor.map (coneInterchangeIso a).hom))
  infer_instance

/-- Original point topology and genuine linear growth discharge both cofiber-excision inputs. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCofiberComparison.lean:119"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem loopedConeCofiberComparison_isStableEquivalence_of_linearGrowth (c : ℕ)
    [∀ n, T1Space ((mappingCone (comparison S)).space n)]
    [∀ n, T1Space ((mappingCone (comparison T)).space n)]
    (hS : ∀ n, TopCat.HomotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{u + 1} ((mappingCone (comparison S)).point n))))
    (hT : ∀ n, TopCat.HomotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{u + 1} ((mappingCone (comparison T)).point n))))
    (hπS : ∀ n x k, k < n + 2 → Subsingleton
      (HomotopyGroup.Pi k ((mappingCone (comparison S)).space (n + c + 2)) x))
    (hπT : ∀ n x k, k < n + 2 → Subsingleton
      (HomotopyGroup.Pi k ((mappingCone (comparison T)).space (n + c + 2)) x)) :
    IsStableEquivalence (loopedConeCofiberComparison a) := by
  apply (mappingConeParameterLoopingComparison_isStableEquivalence_of_linearGrowth
    (E := mappingCone (comparison S)) (F := mappingCone (comparison T))
    (mappingConeMap (strictSquareComparisonFunctor.map a)) c hS hT hπS hπT).comp
  intro d
  change IsIso ((stableHomotopyFunctor d).map
    (parameterLoopingFunctor.map (coneInterchangeIso a).hom))
  infer_instance

end Topology.LoopPrespectrum.StrictSquare


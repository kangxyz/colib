/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassTower
public import Colib.Topology.Prespectrum.TelescopeDiagram

/-!
# The actual original section Bass telescope

The original proved Laurent seed and all its Bass images form the actual reduced telescope.
Coefficient maps act on every original cylinder, strictly functorially. The initial inclusion
is the original stage-zero face. This construction makes no identification with classical Bass
groups and does not assert a nonconnective Thomason–Trobaugh theorem.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original reduced telescope of the proved geometric Bass tower, as a strict ring diagram. -/
def boundedAboveFlatAffineSectionBassTelescopeFunctor : CommRingCat.{u} ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor boundedAboveFlatAffineSectionBassDiagram
    boundedAboveFlatAffineSectionBassTransition

/-- The actual quotient telescope, retaining the same original iterated seed at every stage. -/
def boundedAboveFlatAffineSectionBassTelescope (R : CommRingCat.{u}) : LoopPrespectrum.{u+1} :=
  boundedAboveFlatAffineSectionBassTelescopeFunctor.obj R

/-- The original coefficient map on the constructed Bass telescope. -/
def boundedAboveFlatAffineSectionBassTelescopeMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionBassTelescope R ⟶ boundedAboveFlatAffineSectionBassTelescope S :=
  boundedAboveFlatAffineSectionBassTelescopeFunctor.map f

/-- Every actual Bass stage includes through the original initial face of its cylinder. -/
def boundedAboveFlatAffineSectionBassTelescopeInclusion (i : ℕ) :
    boundedAboveFlatAffineSectionBassDiagram.{u} i ⟶
      boundedAboveFlatAffineSectionBassTelescopeFunctor :=
  Telescope.diagramInclusion _ _ i

/-- The original geometric section prespectrum enters at the unchanged stage-zero face. -/
def boundedAboveFlatAffineSectionBassTelescopeInitial :
    boundedAboveFlatAffineSectionPrespectrumFunctor.{u} ⟶
      boundedAboveFlatAffineSectionBassTelescopeFunctor :=
  boundedAboveFlatAffineSectionBassTelescopeInclusion 0

/-- Identity coefficients induce the literal identity on the actual quotient telescope. -/
theorem boundedAboveFlatAffineSectionBassTelescopeMap_id (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionBassTelescopeMap (𝟙 R) =
      𝟙 (boundedAboveFlatAffineSectionBassTelescope R) :=
  boundedAboveFlatAffineSectionBassTelescopeFunctor.map_id R

/-- Composing coefficients gives the literal composite telescope map. -/
theorem boundedAboveFlatAffineSectionBassTelescopeMap_comp {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineSectionBassTelescopeMap (f ≫ g) =
      boundedAboveFlatAffineSectionBassTelescopeMap f ≫
        boundedAboveFlatAffineSectionBassTelescopeMap g :=
  boundedAboveFlatAffineSectionBassTelescopeFunctor.map_comp f g

/-- The original cylinder coordinate and every actual iterated coefficient map are retained. -/
theorem boundedAboveFlatAffineSectionBassTelescopeMap_cylinder {R S : CommRingCat.{u}}
    (f : R ⟶ S) (k i : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeMap f).map k
        (Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
          (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i (s, x)) =
      Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj S)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app S) k i
          (s, ((boundedAboveFlatAffineSectionBassDiagram i).map f).map k x) := rfl

/-- The initial natural map retains the literal initial face in every original level. -/
theorem boundedAboveFlatAffineSectionBassTelescopeInitial_apply (R : CommRingCat.{u}) (k : ℕ)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeInitial.app R).map k x =
      Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k 0 (0, x) := rfl

/-- Every original telescope cylinder joins consecutive inclusions through the same Bass seed.
-/
def boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy (R : CommRingCat.{u}) (i : ℕ) :
    Homotopy ((boundedAboveFlatAffineSectionBassTelescopeInclusion i).app R)
      ((boundedAboveFlatAffineSectionBassTransition i).app R ≫
        (boundedAboveFlatAffineSectionBassTelescopeInclusion (i + 1)).app R) :=
  Telescope.diagramInclusionHomotopy _ _ R i

/-- Every stage inclusion commutes strictly with arbitrary coefficient maps. -/
theorem boundedAboveFlatAffineSectionBassTelescopeInclusion_naturality
    (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatAffineSectionBassDiagram i).map f ≫
        (boundedAboveFlatAffineSectionBassTelescopeInclusion i).app S =
      (boundedAboveFlatAffineSectionBassTelescopeInclusion i).app R ≫
        boundedAboveFlatAffineSectionBassTelescopeMap f :=
  (boundedAboveFlatAffineSectionBassTelescopeInclusion i).naturality f

/-- The concrete inclusion homotopy is the literal cylinder at the unchanged time. -/
theorem boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy_apply
    (R : CommRingCat.{u}) (i k : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy R i).level k (s, x) =
      Telescope.cylinder (fun j ↦ (boundedAboveFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedAboveFlatAffineSectionBassTransition j).app R) k i (s, x) := rfl

/-- Coefficients preserve the actual homotopy, at the same time and every prespectrum level. -/
theorem boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy_naturality_apply
    {R S : CommRingCat.{u}} (f : R ⟶ S) (i k : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedAboveFlatAffineSectionBassTelescopeMap f).map k
        ((boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy R i).level k (s, x)) =
      (boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy S i).level k
        (s, ((boundedAboveFlatAffineSectionBassDiagram i).map f).map k x) := rfl

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.Scheme.Modules in
attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassTelescope.lean:26-85"
  "adaptation" "Actual quotient telescope, coefficient action and literal cylinder inclusions"]
  boundedAboveFlatAffineSectionBassTelescopeFunctor
  boundedAboveFlatAffineSectionBassTelescope
  boundedAboveFlatAffineSectionBassTelescopeMap
  boundedAboveFlatAffineSectionBassTelescopeInclusion
  boundedAboveFlatAffineSectionBassTelescopeInitial
  boundedAboveFlatAffineSectionBassTelescopeMap_id
  boundedAboveFlatAffineSectionBassTelescopeMap_comp
  boundedAboveFlatAffineSectionBassTelescopeMap_cylinder
  boundedAboveFlatAffineSectionBassTelescopeInitial_apply
  boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy
  boundedAboveFlatAffineSectionBassTelescopeInclusion_naturality
  boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy_apply
  boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy_naturality_apply

open AlgebraicGeometry.Scheme.Modules in
attribute [colib_tag "COL-0362"]
  boundedAboveFlatAffineSectionBassTelescopeFunctor
  boundedAboveFlatAffineSectionBassTelescopeInclusionHomotopy

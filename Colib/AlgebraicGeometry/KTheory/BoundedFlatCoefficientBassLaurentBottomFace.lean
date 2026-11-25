/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientCompositionTracks
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBassProjectionPath
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectProjectionBinaryRows
public import Colib.KTheory.Waldhausen.Iterated.RealizationSimplexComposition
public import Colib.Topology.Realization.SimplexProductGrid

/-!
# The native Laurent composition face of the Bass comparison

The actual two-chart projection path and Laurent binary normalization form
one product simplex; their geometric times remain independent. Adapted from
`BassLaurentBottomFace.lean` in the original BoundedFlat Bass proof at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassLaurentBottomFace

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The Laurent coefficient scheme map induced by `v`. -/
abbrev firstMap := coefficientMap P ((laurentUnderFunctor R).map v)
/-- The Laurent coefficient scheme map induced by `u`. -/
abbrev secondMap := coefficientMap P ((laurentUnderFunctor R).map u)
/-- The source model map of the binary normalization triangle for the two Laurent coefficient
maps. -/
abbrev source := BoundedFlatPerfectBinarySimplex.sourceMap (firstMap P v) (secondMap P u)

/-- The three canonical vertices of the native binary Laurent normalization. -/
abbrev vertices (i : Fin 3) :=
  (BoundedFlatPerfectProjectionBinaryRows.binaryNodes (firstMap P v) (secondMap P u) i).1

/-- The canonical binary Laurent references, including the full normalization comparison. -/
abbrev references (i : Fin 3) : (source P u v).hom.toFunctor ≅
    (vertices P u v i).hom.toFunctor :=
  (BoundedFlatPerfectProjectionBinaryRows.binaryNodes (firstMap P v) (secondMap P u) i).2

/-- Actual composition of the five-vertex Bass projection diagram and Laurent binary triangle. -/
def simplex : ModelSimplex
    (asSmallCategory (W (space (op P, a))))
    (asSmallCategory (W
      (space (op P, (laurentUnderFunctor R).obj c)))) 14 :=
  CommonReferenceProduct.simplex
    (BoundedFlatCoefficientBassProjectionPath.source P a)
    (fun i ↦ (BoundedFlatCoefficientBassProjectionPath.nodes P a i).1)
    (fun i ↦ (BoundedFlatCoefficientBassProjectionPath.nodes P a i).2)
    (source P u v) (vertices P u v) (references P u v)

/-- Both geometric times stay independent in the actual realized grid parameter. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ Topology.SimplexGrid.parameter.{u + 1} 4 2
    (BoundedFlatCoefficientBassProjectionPath.parameter z.2, binaryPath (k := 2) 0 1 2 z.1),
    by fun_prop⟩

/-- The fixed original Laurent-composition homotopy is the native binary path, with its
literal endpoint casts and its two original normalization pieces. -/
theorem laurent_native (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (W
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    prespectrumSimplexFamily (ModelSimplex.ofIsos (source P u v)
      (vertices P u v) (references P u v)) n (binaryPath (k := 2) 0 1 2 r, x) =
      (boundedAboveFlatCoefficientLaurentCompositionHomotopy P u v).level n (r, x) := by
  have hd : ModelSimplex.ofIsos (source P u v) (vertices P u v) (references P u v) =
      BoundedFlatPerfectBinarySimplex.simplex (firstMap P v) (secondMap P u) := by
    unfold BoundedFlatPerfectBinarySimplex.simplex
    refine ModelSimplex.ofIsos_nodes_congr
      (BoundedFlatPerfectProjectionBinaryRows.binaryNodes (firstMap P v) (secondMap P u))
      (fun i ↦ ⟨(![BoundedFlatPerfectBinarySimplex.sourceMap (firstMap P v) (secondMap P u),
        BoundedFlatPerfectBinarySimplex.intermediateMap (firstMap P v) (secondMap P u),
        BoundedFlatPerfectBinarySimplex.targetMap (firstMap P v) (secondMap P u)] : Fin 3 → _) i,
        Fin.cases (Iso.refl _) (Fin.cases
          (BoundedFlatPerfectBinarySimplex.first (firstMap P v) (secondMap P u))
          (Fin.cases (BoundedFlatPerfectBinarySimplex.total (firstMap P v) (secondMap P u))
            (fun j ↦ Fin.elim0 j))) i⟩) ?_
    intro i
    fin_cases i <;> rfl
  rw [hd]
  exact BoundedFlatPerfectBinarySimplex.native_path (firstMap P v) (secondMap P u) n r x

/-- The complete prescribed bottom face of the original Bass interior cube, for every original
level, both independent times and every original overlap input. -/
theorem native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (parameter.{u} (r, t), x) =
      (Homotopy.precomp (boundedAboveFlatCoefficientBassSquareComparison P a)
        (boundedAboveFlatCoefficientLaurentCompositionHomotopy P u v)).level n
        (r, HomotopyPushout.cylinder
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a))
          (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  refine (CommonReferenceProduct.prespectrum_comp
    (BoundedFlatCoefficientBassProjectionPath.source P a)
    (fun i ↦ (BoundedFlatCoefficientBassProjectionPath.nodes P a i).1)
    (fun i ↦ (BoundedFlatCoefficientBassProjectionPath.nodes P a i).2)
    (source P u v) (vertices P u v) (references P u v) n x
    (BoundedFlatCoefficientBassProjectionPath.parameter t) (binaryPath (k := 2) 0 1 2 r)).trans ?_
  change prespectrumSimplexFamily (ModelSimplex.ofIsos (source P u v)
      (vertices P u v) (references P u v)) n
    (binaryPath (k := 2) 0 1 2 r,
      prespectrumSimplexFamily (BoundedFlatCoefficientBassProjectionPath.simplex P a) n
        (BoundedFlatCoefficientBassProjectionPath.parameter t, x)) = _
  rw [BoundedFlatCoefficientBassProjectionPath.native P a n t x, laurent_native]
  rfl

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassLaurentBottomFace

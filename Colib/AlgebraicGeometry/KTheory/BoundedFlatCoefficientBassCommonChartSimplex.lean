/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassOverlapReference
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBassScalarComparison
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceWhiskering
public import Colib.KTheory.Waldhausen.Iterated.SimplexWhiskering
public import Colib.KTheory.Waldhausen.Iterated.SimplexPrespectrumFaceEvaluation

/-!
# The actual common-reference simplex of both Bass charts

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassCommonChartSimplex.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassOverlap
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The original dependent nodes retain all reference isomorphisms of the original chart. -/
def chartNodes (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) :=
  BoundedFlatPerfectDoubleSquareMergedSimplex.nodes
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
    (coefficientMap P (α.app c))
    (by rw [← coefficientMap_comp, ← coefficientMap_comp, α.naturality])
    (by rw [← coefficientMap_comp, ← coefficientMap_comp, α.naturality])

/-- Every overlap node stores its full actual functor and common reference isomorphism. -/
abbrev Node := Σ F : asSmallCategory (W (space (op P, a))) ⟶
    asSmallCategory (W
      (space (op P, (laurentUnderFunctor R).obj c))),
    (commonReference P u v).hom.toFunctor ≅ F.hom.toFunctor

/-- Precompose the whole original chart node; the reference uses the actual projection equation. -/
def chartOverlapNodes (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hα : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (i : Fin 18) : Node P u v :=
  ⟨projectionMap P (a := a) ≫ (chartNodes P u v α i).1,
    commonToChartReference P u v α hα ≪≫
      isoWhiskerLeft (projectionMap P (a := a)).hom.toFunctor (chartNodes P u v α i).2⟩

/-- The entire chart diagram after literal overlap precomposition and reference change. -/
theorem chartOverlap_simplex (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hα : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    ModelSimplex.ofIsos (commonReference P u v)
      (fun i ↦ (chartOverlapNodes P u v α hα i).1)
      (fun i ↦ (chartOverlapNodes P u v α hα i).2) =
      (BoundedFlatPerfectBassScalarComparison.simplex P α u v).precomp
        (projectionMap P (a := a)) := by
  unfold chartOverlapNodes
  rw [ModelSimplex.ofIsos_change_reference, ← ModelSimplex.ofIsos_precomp]
  rfl

/-- Both chart diagrams use the same actual Laurent total reference. Opposite-chart slots remain
separate: no shared-boundary equality is inferred merely from this concatenation. -/
def nodes : Fin 36 → Node P u v :=
  Fin.addCases (m := 18) (n := 18) (motive := fun _ ↦ Node P u v)
    (chartOverlapNodes P u v (underToLaurent R) (laurentPlus_projection P c))
    (chartOverlapNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c))

/-- One genuine 35-simplex on the original overlap retains both whole chart diagrams. -/
def simplex : ModelSimplex
    (asSmallCategory (W (space (op P, a))))
    (asSmallCategory (W
      (space (op P, (laurentUnderFunctor R).obj c)))) 35 :=
  ModelSimplex.ofIsos (commonReference P u v)
    (fun i ↦ (nodes P u v i).1) (fun i ↦ (nodes P u v i).2)

/-- The face inclusion selecting the first 18 vertices, which carry the positive chart diagram. -/
def plusFace : ⦋17⦌ ⟶ ⦋35⦌ :=
  SimplexCategory.Hom.mk ⟨Fin.castAdd 18, fun _ _ h ↦ h⟩

/-- The face inclusion selecting the final 18 vertices, which carry the inverse-coordinate chart
diagram. -/
def minusFace : ⦋17⦌ ⟶ ⦋35⦌ :=
  SimplexCategory.Hom.mk ⟨Fin.natAdd 18, fun _ _ h ↦ Nat.add_le_add_left h 18⟩

/-- The full positive original diagram survives, not just its vertices or endpoint maps. -/
theorem plus_face : (simplex P u v).face plusFace =
    (BoundedFlatPerfectBassScalarComparison.simplex P (underToLaurent R) u v).precomp
      (projectionMap P (a := a)) := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _
    (chartOverlapNodes P u v (underToLaurent R) (laurentPlus_projection P c))
    (fun i ↦ by
      change nodes P u v (Fin.castAdd 18 i) = _
      unfold nodes
      rw [Fin.addCases_left])).trans (chartOverlap_simplex P u v _ _)

/-- The full inverse-coordinate diagram survives with its original reference transformations. -/
theorem minus_face : (simplex P u v).face minusFace =
    (BoundedFlatPerfectBassScalarComparison.simplex P (underToLaurentInvert R) u v).precomp
      (projectionMap P (a := a)) := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _
    (chartOverlapNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c))
    (fun i ↦ by
      change nodes P u v (Fin.natAdd 18 i) = _
      unfold nodes
      rw [Fin.addCases_right])).trans (chartOverlap_simplex P u v _ _)

/-- At every simplex parameter, the common positive face is the original overlap evaluation. -/
theorem plus_family (n : ℕ) (z : StdSimplex ℝ (Fin 18))
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (StdSimplex.map plusFace.toOrderHom z, x) =
      prespectrumSimplexFamily
        (BoundedFlatPerfectBassScalarComparison.simplex P (underToLaurent R) u v) n
        (z, (boundedAboveFlatPerfectPullbackPrespectrumMap
          (polynomialProjection P a)).map n x) := by
  rw [prespectrumSimplexFamily_face, plus_face, prespectrumSimplexFamily_precomp,
    projectionMap_prespectrum]
  rfl

/-- At every simplex parameter, the common negative face is the original overlap evaluation. -/
theorem minus_family (n : ℕ) (z : StdSimplex ℝ (Fin 18))
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (StdSimplex.map minusFace.toOrderHom z, x) =
      prespectrumSimplexFamily
        (BoundedFlatPerfectBassScalarComparison.simplex P (underToLaurentInvert R) u v) n
        (z, (boundedAboveFlatPerfectPullbackPrespectrumMap
          (polynomialProjection P a)).map n x) := by
  rw [prespectrumSimplexFamily_face, minus_face, prespectrumSimplexFamily_precomp,
    projectionMap_prespectrum]
  rfl

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassOverlap

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.ConnectorMonoCoherence
public import Colib.Topology.Realization.OrderedCoverNerve
public import Colib.Topology.Realization.NumerableConnectorCover
public import Colib.Topology.Realization.DescAcross
public import Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit

/-!
# The actual return map from the ordered cover nerve

The map is constructed on nondegenerate simplices using ordered connector
interpolation. Proven mono coherence descends it through the nonsingular
simplex colimit. Degenerate charts use the canonical epi to their unique
nondegenerate image, so repeated weights are pushed forward and summed
BEFORE interpolation. No associativity or desired domination map is assumed.
-/

open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/Realization/OrderedNerveRealizationMap.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Convexity CategoryTheory CategoryTheory.Limits Opposite
open scoped Topology unitInterval Simplicial
universe u v w
namespace Topology.NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A] {ι : Type v} [LinearOrder ι] {κ : Type w}
variable (E : LocalEquiconnection A) (W : ι → Set A) (V : κ → Set A)
variable (hconvex : ∀ k, E.IsConvex (V k)) (href : PointStarRefines W V)
variable (vertex : ι → A) (hvertex : ∀ i, vertex i ∈ W i)

/-- The actual selected target vertices of a simplex of the ordered cover nerve. -/
def nerveVertices {n : ℕ} (s : (orderedNerve W).toSSet.obj (op ⦋n⦌)) : Fin (n + 1) → A :=
  fun i ↦ vertex (s.1.obj i)

include hconvex href hvertex in
/-- The common point and point-star refinement prove geometric admissibility. -/
theorem nerveVertices_admissible {n : ℕ} (s : (orderedNerve W).toSSet.obj (op ⦋n⦌)) :
    AdmissibleVertices E (nerveVertices W vertex s) := by
  obtain ⟨x, hx⟩ := s.2
  obtain ⟨k, hk⟩ := href x
  exact ⟨V k, hconvex k, fun i ↦ hk ⟨s.1.obj i, hx i, hvertex (s.1.obj i)⟩⟩

/-- The actual chart map on a nondegenerate simplex, in its original realized coordinates. -/
def nerveReturnChart (s : (orderedNerve W).toSSet.N) :
    C(|SSet.stdSimplex.{v}.obj ⦋s.dim⦌|, A) :=
  (interpolate E (nerveVertices W vertex s.simplex)
    (nerveVertices_admissible E W V hconvex href vertex hvertex s.simplex)).comp
      ⟨SimplexCategory.toTopHomeo.{v} ⦋s.dim⦌,
        (SimplexCategory.toTopHomeo.{v} ⦋s.dim⦌).continuous⟩

/-- The chart family satisfies every morphism in the nondegenerate-face diagram. -/
theorem nerveReturnChart_naturality {s t : (orderedNerve W).toSSet.N} (f : s ⟶ t)
    (x : |SSet.stdSimplex.{v}.obj ⦋s.dim⦌|) :
    nerveReturnChart E W V hconvex href vertex hvertex t
      (SSet.toTop.map (SSet.stdSimplex.{v}.map (SSet.N.monoOfLE (leOfHom f))) x) =
        nerveReturnChart E W V hconvex href vertex hvertex s x := by
  let φ := SSet.N.monoOfLE (leOfHom f)
  have hv : nerveVertices W vertex t.simplex ∘ φ.toOrderHom =
      nerveVertices W vertex s.simplex := by
    funext i
    exact congrArg (fun z : (orderedNerve W).toSSet.obj (op ⦋s.dim⦌) ↦ vertex (z.1.obj i))
      (SSet.N.map_monoOfLE (leOfHom f))
  change interpolate E (nerveVertices W vertex t.simplex) _
      (SimplexCategory.toTopHomeo.{v} ⦋t.dim⦌
        (SSet.toTop.map (SSet.stdSimplex.{v}.map φ) x)) = _
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  change interpolate E (nerveVertices W vertex t.simplex) _
    ((SimplexCategory.toTopHomeo.{v} ⦋s.dim⦌ x).map φ.toOrderHom) = _
  rw [interpolate_mono]
  change interpolate E _ _ _ = interpolate E (nerveVertices W vertex s.simplex) _ _
  simp only [hv]
  rfl

/-- The genuinely constructed continuous return map on the actual weak realization. -/
def nerveReturnMap : C(|(orderedNerve W).toSSet|, A) :=
  TopCat.colimitDescAcross
    (SSet.toTop.mapCocone ((orderedNerve W).toSSet.coconeN'))
    (isColimitOfPreserves SSet.toTop ((orderedNerve W).toSSet.isColimitCoconeN'))
    (nerveReturnChart E W V hconvex href vertex hvertex)
    (fun f x ↦ nerveReturnChart_naturality E W V hconvex href vertex hvertex f x)

/-- The descended map retains every original nondegenerate chart exactly. -/
theorem nerveReturnMap_nondegenerate (s : (orderedNerve W).toSSet.N)
    (x : StdSimplex ℝ (Fin (s.dim + 1))) :
    nerveReturnMap E W V hconvex href vertex hvertex (realizationSimplex s.simplex x) =
      interpolate E (nerveVertices W vertex s.simplex)
        (nerveVertices_admissible E W V hconvex href vertex hvertex s.simplex) x := by
  have h := TopCat.colimitDescAcross_ι
    (SSet.toTop.mapCocone ((orderedNerve W).toSSet.coconeN'))
    (isColimitOfPreserves SSet.toTop ((orderedNerve W).toSSet.isColimitCoconeN'))
    (nerveReturnChart E W V hconvex href vertex hvertex)
    (fun f x ↦ nerveReturnChart_naturality E W V hconvex href vertex hvertex f x)
    s ((SimplexCategory.toTopHomeo.{v} ⦋s.dim⦌).symm x)
  change nerveReturnMap E W V hconvex href vertex hvertex (realizationSimplex s.simplex x) =
    interpolate E (nerveVertices W vertex s.simplex)
      (nerveVertices_admissible E W V hconvex href vertex hvertex s.simplex)
      (SimplexCategory.toTopHomeo.{v} ⦋s.dim⦌
        ((SimplexCategory.toTopHomeo.{v} ⦋s.dim⦌).symm x)) at h
  simpa only [Homeomorph.apply_symm_apply] using h

/-- Every repeated-vertex chart first aggregates coefficients through its canonical epi
and only then evaluates the nondegenerate ordered interpolation. -/
theorem nerveReturnMap_aggregated (s : (orderedNerve W).toSSet.S)
    (x : StdSimplex ℝ (Fin (s.dim + 1))) :
    nerveReturnMap E W V hconvex href vertex hvertex (realizationSimplex s.simplex x) =
      interpolate E (nerveVertices W vertex s.toN.simplex)
        (nerveVertices_admissible E W V hconvex href vertex hvertex s.toN.simplex)
        (x.map s.toNπ.toOrderHom) := by
  have hx : realizationSimplex s.toN.simplex (x.map s.toNπ.toOrderHom) =
      realizationSimplex s.simplex x := by
    change realizationSimplex s.toN.simplex (StdSimplex.map s.toNπ x) = _
    rw [realizationSimplex_naturality, SSet.S.map_toNπ_op_apply]
  rw [← hx]
  exact nerveReturnMap_nondegenerate E W V hconvex href vertex hvertex s.toN _

/-- The actual return map preserves every convex carrier containing an original
simplex's selected vertices, including for degenerate original simplices. -/
theorem nerveReturnMap_mem (s : (orderedNerve W).toSSet.S)
    (x : StdSimplex ℝ (Fin (s.dim + 1))) {U : Set A} (hU : E.IsConvex U)
    (hv : ∀ i, nerveVertices W vertex s.simplex i ∈ U) :
    nerveReturnMap E W V hconvex href vertex hvertex (realizationSimplex s.simplex x) ∈ U := by
  rw [nerveReturnMap_aggregated]
  apply interpolate_mem E _ _ hU
  intro j
  obtain ⟨i, rfl⟩ := (SimplexCategory.epi_iff_surjective (f := s.toNπ)).mp
    (inferInstance : Epi s.toNπ) j
  have he : nerveVertices W vertex s.toN.simplex (s.toNπ.toOrderHom i) =
      nerveVertices W vertex s.simplex i :=
    congrArg (fun z : (orderedNerve W).toSSet.obj (op ⦋s.dim⦌) ↦ vertex (z.1.obj i))
      (SSet.S.map_toNπ_op_apply s)
  rw [he]
  exact hv i

end Topology.NumerableConnectorCover

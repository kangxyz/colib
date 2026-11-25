/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputNative

/-!
# Whole scalar face transport for global evaluation charts

Affine face transport preserves every point of the selected native comparison. Endpoint casts
only identify the original scalar paths; they do not replace the two-dimensional family.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputParameter
variable {k l : ℕ} (α : ⦋k⦌ ⟶ ⦋l⦌)
variable {i j m : Fin (k + 1)}

/-- The original scalar path evaluated in the actual affine face. -/
def reindexPath (p : Path (StdSimplex.single i : StdSimplex ℝ (Fin (k + 1)))
    (StdSimplex.single j)) :
    Path (StdSimplex.single (α.toOrderHom i) : StdSimplex ℝ (Fin (l + 1)))
      (StdSimplex.single (α.toOrderHom j)) where
  toFun t := StdSimplex.map α.toOrderHom (p t)
  continuous_toFun := by fun_prop
  source' := by rw [p.source]; exact StdSimplex.map_single _ _
  target' := by rw [p.target]; exact StdSimplex.map_single _ _

/-- The complete two-coordinate family is mapped without any reparametrization. -/
def reindexHomotopy {p q : Path (StdSimplex.single i : StdSimplex ℝ (Fin (k + 1)))
    (StdSimplex.single j)} (J : p.Homotopy q) :
    (reindexPath α p).Homotopy (reindexPath α q) where
  toFun z := StdSimplex.map α.toOrderHom (J z)
  continuous_toFun := by fun_prop
  map_zero_left t := congrArg (StdSimplex.map α.toOrderHom) (J.apply_zero t)
  map_one_left t := congrArg (StdSimplex.map α.toOrderHom) (J.apply_one t)
  prop' r t ht := congrArg (StdSimplex.map α.toOrderHom) (J.eq_fst r ht)

/-- The entire edge, rather than only its endpoints, is the corresponding affine edge. -/
theorem reindexPath_edge : reindexPath α (edge i j) = edge (α.toOrderHom i) (α.toOrderHom j) := by
  apply Path.ext
  funext t
  exact StdSimplex.map_duple (unitInterval.nonneg (unitInterval.symm t))
    (unitInterval.nonneg t) (by simp) i j α.toOrderHom

/-- Face transport preserves the literal two halves, including their common midpoint. -/
theorem reindexPath_trans
    (p : Path (StdSimplex.single i : StdSimplex ℝ (Fin (k + 1))) (StdSimplex.single j))
    (q : Path (StdSimplex.single j : StdSimplex ℝ (Fin (k + 1))) (StdSimplex.single m)) :
    reindexPath α (p.trans q) = (reindexPath α p).trans (reindexPath α q) := by
  apply Path.ext
  funext t
  change StdSimplex.map α.toOrderHom ((p.trans q) t) = _
  rw [Path.trans_apply, Path.trans_apply]
  split <;> rfl

/-- A proved entire face equality lifts all original native coordinates. -/
theorem reindex_native {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (S : ModelSimplex V W k) (T : ModelSimplex V W l)
    (hface : T.face α = S)
    {p q : Path (StdSimplex.single i : StdSimplex ℝ (Fin (k + 1))) (StdSimplex.single j)}
    (J : p.Homotopy q) {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
    (N : H.RelHomotopy K) (h : HomotopyLift S J N) :
    HomotopyLift T (reindexHomotopy α J) N := by
  intro n r s x
  change prespectrumSimplexFamily T n (StdSimplex.map α.toOrderHom (J (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, hface]
  exact h n r s x

/-- The complete original chart word in any chosen five-vertex face. -/
def chart (α : ⦋4⦌ ⟶ ⦋7⦌) :
    ((edge (α.toOrderHom 0) (α.toOrderHom 3)).trans
      (edge (α.toOrderHom 3) (α.toOrderHom 4))).Homotopy
    ((edge (α.toOrderHom 0) (α.toOrderHom 1)).trans
      ((edge (α.toOrderHom 1) (α.toOrderHom 2)).trans
        (edge (α.toOrderHom 2) (α.toOrderHom 4)))) :=
  (reindexHomotopy α InputSimplex.compositionParameter.symm).cast
    (by
      change reindexPath α ((edge 0 3).trans (edge 3 4)) = _
      simp only [reindexPath_trans, reindexPath_edge])
    (by
      change reindexPath α ((edge 0 1).trans ((edge 1 2).trans (edge 2 4))) = _
      simp only [reindexPath_trans, reindexPath_edge])

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputParameter

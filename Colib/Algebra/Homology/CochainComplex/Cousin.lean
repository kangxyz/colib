/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The Cousin complex of a finite support tower

The adjacent support windows are concentrated in their codimension degree.
Their connecting maps give the Cousin differential. The stage at codimension
zero computes the homology of this complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type*} [Category* A] [Abelian A]

/-- The localization sequences of a finite support tower whose layers are
concentrated on the diagonal. In both families the second index is the
cohomological degree. -/
structure ExactSupportTower (A : Type*) [Category* A] [Abelian A] where
  /-- The object of the support stage at filtration index `p` and degree `n`. -/
  stage : ℕ → ℕ → A
  /-- The adjacent relative layer at filtration index `p` and degree `n`. -/
  layer : ℕ → ℕ → A
  /-- The map from the next support stage into the current stage. -/
  transition : ∀ p n, stage (p + 1) n ⟶ stage p n
  /-- The map from a support stage to its adjacent relative layer. -/
  toLayer : ∀ p n, stage p n ⟶ layer p n
  /-- The connecting map from a relative layer to the next support stage in degree `n + 1`. -/
  boundary : ∀ p n, layer p n ⟶ stage (p + 1) (n + 1)
  transition_toLayer_zero : ∀ p n, transition p n ≫ toLayer p n = 0
  toLayer_boundary_zero : ∀ p n, toLayer p n ≫ boundary p n = 0
  boundary_transition_zero : ∀ p n, boundary p n ≫ transition p (n + 1) = 0
  exact_stage : ∀ p n,
    (ShortComplex.mk _ _ (transition_toLayer_zero p n)).Exact
  exact_layer : ∀ p n,
    (ShortComplex.mk _ _ (toLayer_boundary_zero p n)).Exact
  exact_boundary : ∀ p n,
    (ShortComplex.mk _ _ (boundary_transition_zero p n)).Exact
  /-- The filtration bound above which all support stages vanish. -/
  dimension : ℕ
  isZero_stage : ∀ p n, dimension < p → IsZero (stage p n)
  isZero_off_diagonal : ∀ p n, p ≠ n → IsZero (layer p n)

namespace ExactSupportTower

variable (T : ExactSupportTower A)

private theorem epi_transition (p n : ℕ) (h : p ≠ n) : Epi (T.transition p n) :=
  (T.exact_stage p n).epi_f ((T.isZero_off_diagonal p n h).eq_of_tgt _ _)

private theorem mono_transition_succ (p n : ℕ) (h : p ≠ n) :
    Mono (T.transition p (n + 1)) :=
  (T.exact_boundary p n).mono_g ((T.isZero_off_diagonal p n h).eq_of_src _ _)

private theorem isZero_stage_of_degree_lt {p n : ℕ} (h : n < p) :
    IsZero (T.stage p n) := by
  have descend (length : ℕ) : ∀ q, n < q → T.dimension < q + length →
      IsZero (T.stage q n) := by
    induction length with
    | zero =>
      intro q _ hq
      exact T.isZero_stage q n (by simpa using hq)
    | succ length ih =>
      intro q hn hq
      let : Epi (T.transition q n) := epi_transition T q n (by omega)
      exact IsZero.of_epi (T.transition q n) (ih (q + 1) (by omega) (by omega))
  exact descend (T.dimension + 1) p h (by omega)

private theorem mono_toLayer (p : ℕ) : Mono (T.toLayer p p) :=
  (T.exact_stage p p).mono_g
    ((isZero_stage_of_degree_lt T (Nat.lt_succ_self p)).eq_of_src _ _)

/-- The Cousin differential is the localization boundary followed by
projection to the next layer. -/
def differential (p : ℕ) : T.layer p p ⟶ T.layer (p + 1) (p + 1) :=
  T.boundary p p ≫ T.toLayer (p + 1) (p + 1)

theorem differential_comp (p : ℕ) : T.differential p ≫ T.differential (p + 1) = 0 := by
  simp only [differential, Category.assoc]
  rw [← Category.assoc (T.toLayer _ _), T.toLayer_boundary_zero, zero_comp, comp_zero]

/-- The terms and the original localization differentials of the Cousin complex. -/
abbrev cochainComplex : CochainComplex A ℕ :=
  CochainComplex.of (fun p ↦ T.layer p p) T.differential T.differential_comp

/-- The Cousin complex vanishes above the finite bound of the support tower. -/
theorem isZero_cochainComplex_X_of_dimension_lt (p : ℕ) (h : T.dimension < p) :
    IsZero (T.cochainComplex.X p) := by
  exact (T.exact_layer p p).isZero_X₂
    ((T.isZero_stage p p h).eq_of_src _ _)
    ((T.isZero_stage (p + 1) (p + 1) (Nat.lt_trans h (Nat.lt_succ_self p))).eq_of_tgt _ _)

theorem toLayer_differential_zero (p : ℕ) :
    T.toLayer p p ≫ T.differential p = 0 := by
  rw [differential, ← Category.assoc, T.toLayer_boundary_zero, zero_comp]

/-- In particular the map from the unrestricted degree-zero stage is the
kernel of the first differential. -/
@[no_expose]
def isKernelDifferential (p : ℕ) :
    IsLimit (KernelFork.ofι (T.toLayer p p) (T.toLayer_differential_zero p)) := by
  let : Mono (T.toLayer p p) := mono_toLayer T p
  let : Mono (T.toLayer (p + 1) (p + 1)) := mono_toLayer T (p + 1)
  exact isKernelCompMono (T.exact_layer p p).fIsKernel
    (T.toLayer (p + 1) (p + 1)) rfl

private def stageIsoBaseSucc (n p : ℕ) (h : p ≤ n) :
    T.stage p (n + 1) ≅ T.stage 0 (n + 1) := by
  induction p with
  | zero => exact Iso.refl _
  | succ p ih =>
    let : Epi (T.transition p (n + 1)) := epi_transition T p (n + 1) (by omega)
    let : Mono (T.transition p (n + 1)) := mono_transition_succ T p n (by omega)
    let : IsIso (T.transition p (n + 1)) := isIso_of_mono_of_epi _
    exact asIso (T.transition p (n + 1)) ≪≫ ih (by omega)

private abbrev diagonalShortComplex (p : ℕ) : ShortComplex A :=
  ShortComplex.mk (T.differential p) (T.differential (p + 1)) (T.differential_comp p)

set_option backward.isDefEq.respectTransparency false in
private def diagonalLeftHomologyData (p : ℕ) :
    (diagonalShortComplex T p).LeftHomologyData := by
  let S := diagonalShortComplex T p
  let : Epi (T.transition p (p + 1)) := epi_transition T p (p + 1) (by omega)
  let : Mono (T.toLayer (p + 1) (p + 1)) := mono_toLayer T (p + 1)
  let h := T.isKernelDifferential (p + 1)
  have hlift : h.lift (KernelFork.ofι S.f S.zero) = T.boundary p p := by
    apply (cancel_mono (T.toLayer (p + 1) (p + 1))).1
    exact h.fac _ WalkingParallelPair.zero
  have hcolim (b : T.layer p p ⟶ T.stage (p + 1) (p + 1)) (hb : b = T.boundary p p)
      (w : b ≫ T.transition p (p + 1) = 0) :
      IsColimit (CokernelCofork.ofπ (T.transition p (p + 1)) w) := by
    subst b
    exact (T.exact_boundary p p).gIsCokernel
  refine
    { K := T.stage (p + 1) (p + 1)
      H := T.stage p (p + 1)
      i := T.toLayer (p + 1) (p + 1)
      π := T.transition p (p + 1)
      wi := T.toLayer_differential_zero (p + 1)
      hi := h
      wπ := by rw [hlift]; exact T.boundary_transition_zero p p
      hπ := hcolim _ hlift _ }

/-- A positive degree of the Cousin complex computes the same degree of
the unrestricted stage, via the original map from cycles. -/
@[no_expose]
def homologySuccIso (p : ℕ) :
    T.cochainComplex.homology (p + 1) ≅ T.stage 0 (p + 1) := by
  let K := T.cochainComplex
  let S := diagonalShortComplex T p
  have hprev : (ComplexShape.up ℕ).prev (p + 1) = p :=
    (ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl)
  have hnext : (ComplexShape.up ℕ).next (p + 1) = p + 1 + 1 :=
    (ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel (p + 1) (p + 1 + 1) from rfl)
  let e : K.sc' p (p + 1) (p + 1 + 1) ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [K, S, cochainComplex, diagonalShortComplex])
      (by simp [K, S, cochainComplex, diagonalShortComplex])
  exact K.homologyIsoSc' _ _ _ hprev hnext ≪≫ ShortComplex.homologyMapIso e ≪≫
    (diagonalLeftHomologyData T p).homologyIso ≪≫ stageIsoBaseSucc T p p le_rfl

/-- Vanishing in the unrestricted stage gives exactness of the Cousin complex
in the corresponding positive degree. -/
theorem exactAt_succ (p : ℕ) (h : IsZero (T.stage 0 (p + 1))) :
    T.cochainComplex.ExactAt (p + 1) :=
  (T.cochainComplex.exactAt_iff_isZero_homology (p + 1)).2
    (h.of_iso (T.homologySuccIso p))

variable {B : Type*} [Category* B] [Abelian B]
  (G : A ⥤ B) [G.PreservesZeroMorphisms] [G.PreservesHomology]

/-- Apply an exact functor to the original support stages and localization maps. -/
def map : ExactSupportTower B where
  stage p n := G.obj (T.stage p n)
  layer p n := G.obj (T.layer p n)
  transition p n := G.map (T.transition p n)
  toLayer p n := G.map (T.toLayer p n)
  boundary p n := G.map (T.boundary p n)
  transition_toLayer_zero p n := by rw [← G.map_comp, T.transition_toLayer_zero, G.map_zero]
  toLayer_boundary_zero p n := by rw [← G.map_comp, T.toLayer_boundary_zero, G.map_zero]
  boundary_transition_zero p n := by rw [← G.map_comp, T.boundary_transition_zero, G.map_zero]
  exact_stage p n := (T.exact_stage p n).map G
  exact_layer p n := (T.exact_layer p n).map G
  exact_boundary p n := (T.exact_boundary p n).map G
  dimension := T.dimension
  isZero_stage p n hp := G.map_isZero (T.isZero_stage p n hp)
  isZero_off_diagonal p n hp := G.map_isZero (T.isZero_off_diagonal p n hp)

/-- Applying an exact functor to the tower maps the same Cousin complex. -/
def mapCochainComplexIso :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj T.cochainComplex ≅
      (T.map G).cochainComplex := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) ?_
  intro i j hij
  obtain rfl : i + 1 = j := hij
  simp [cochainComplex, differential, map, G.map_comp]

end ExactSupportTower

end CategoryTheory

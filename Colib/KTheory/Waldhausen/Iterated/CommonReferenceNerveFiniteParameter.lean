/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNervePointwiseFamily
public import Colib.Topology.Realization.SimplexCylinder
public import Colib.Topology.Realization.SimplexProductGrid

/-!
# A whole reference nerve with one finite simplex parameter

The original product-simplex homeomorphism permits an arbitrary first nerve and a finite
second parameter. The characteristic-map law retains every full dependent node of the
lexicographic grid. Its vertex restrictions are the actual induced full-node maps.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor MonoidalCategory Convexity Opposite Topology TopCat SSet
open CategoryTheory.Waldhausen SmallWaldhausenCategory
open scoped Simplicial Topology
universe u
namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.FiniteParameter
variable {V W V' W' : WideSubcategory preservesZero.{u}} (E : V ⟶ W) (F : V' ⟶ W')
variable {q : ℕ} (f : Node E → Fin (q + 1) → Node F)

/-- The whole source chain and the finite parameter chain determine their exact target chain. -/
def simplicial : nerve (Codiscrete (Node E)) ⊗ Δ[q] ⟶ nerve (Codiscrete (Node F)) where
  app n := ↾fun z ↦ Codiscrete.functor
    (fun i ↦ f (z.1.obj i).as (z.2.down.toOrderHom i))
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro z
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j g
    apply Subsingleton.elim

/-- Restriction to every ordered finite face retains its complete node function. -/
theorem simplicial_restrict {m : ℕ} (h : ⦋m⦌ ⟶ ⦋q⦌) :
    nerve (Codiscrete (Node E)) ◁ SSet.stdSimplex.map h ≫ simplicial E F f =
      simplicial E F (fun e i ↦ f e (h.toOrderHom i)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j g
  apply Subsingleton.elim

/-- The initial simplicial endpoint is the exact induced full-node map. -/
theorem simplicial_zero (g : Node E → Fin 2 → Node F) :
    SSet.ι₀ ≫ simplicial E F g =
      nerveMap (Codiscrete.functorOfFun (fun e ↦ g e 0)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j h
  apply Subsingleton.elim

/-- The terminal simplicial endpoint retains the separately specified last full node. -/
theorem simplicial_one (g : Node E → Fin 2 → Node F) :
    SSet.ι₁ ≫ simplicial E F g =
      nerveMap (Codiscrete.functorOfFun (fun e ↦ g e 1)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j h
  apply Subsingleton.elim

/-- Every finite source characteristic map uses the original lexicographic product grid. -/
def gridNodes {p : ℕ} (N : Fin (p + 1) → Node E)
    (i : Fin (SimplexGrid.dimension p q + 1)) : Node F :=
  f (N ((SimplexGrid.indexEquiv p q).symm i).1)
    ((SimplexGrid.indexEquiv p q).symm i).2

@[simp]
theorem gridNodes_index {p : ℕ} (N : Fin (p + 1) → Node E)
    (i : Fin (p + 1)) (j : Fin (q + 1)) :
    gridNodes E F f N (SimplexGrid.index p q (i, j)) = f (N i) j := by
  unfold gridNodes
  rw [SimplexGrid.decode_index]

/-- The restriction is an equality of simplicial maps with all references retained. -/
theorem simplicial_characteristic {p : ℕ} (N : Fin (p + 1) → Node E) :
    simplexMap E N ▷ Δ[q] ≫ simplicial E F f =
      SimplexGrid.embedding p q ≫ simplexMap F (gridNodes E F f N) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · change Codiscrete.mk (f (N (z.1.down.toOrderHom i)) (z.2.down.toOrderHom i)) =
      Codiscrete.mk (gridNodes E F f N
        (SimplexGrid.index p q (z.1.down.toOrderHom i, z.2.down.toOrderHom i)))
    rw [gridNodes_index]
  · intro i j g
    apply Subsingleton.elim

/-- Only the finite second factor is inverted in the actual realization-product comparison. -/
def parameter : C(|nerve (Codiscrete (Node E))| × StdSimplex ℝ (Fin (q + 1)),
    |nerve (Codiscrete (Node F))|) :=
  (SSet.toTop.map (simplicial E F f)).hom.comp
    ((realizationProductSimplexIso (nerve (Codiscrete (Node E))) q).inv.hom.comp
      ⟨fun z ↦ (z.1, (SimplexCategory.toTopHomeo ⦋q⦌).symm z.2),
        continuous_fst.prodMk
          ((SimplexCategory.toTopHomeo ⦋q⦌).symm.continuous.comp continuous_snd)⟩)

/-- Every finite characteristic map recovers the unchanged realized product parameter. -/
theorem parameter_characteristic {p : ℕ} (N : Fin (p + 1) → Node E)
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    parameter E F f (CommonReferenceNerve.parameter E N z, w) =
      CommonReferenceNerve.parameter F (gridNodes E F f N)
        (SimplexGrid.parameter.{u} p q (z, w)) := by
  let z₀ : (|(Δ[p] : SSet.{u})| ⊗ |(Δ[q] : SSet.{u})| : TopCat.{u}) :=
    ((SimplexCategory.toTopHomeo ⦋p⦌).symm z,
      (SimplexCategory.toTopHomeo ⦋q⦌).symm w)
  let y := (realizationProductSimplexIso (Δ[p] : SSet.{u}) q).inv z₀
  let barycentric : (|(Δ[p] : SSet.{u})| ⊗ |(Δ[q] : SSet.{u})| : TopCat.{u}) →
      StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1)) :=
    fun t ↦ (SimplexCategory.toTopHomeo ⦋p⦌ t.1,
      SimplexCategory.toTopHomeo ⦋q⦌ t.2)
  have hy : realizationProductSimplexHomeomorph p q y = (z, w) := by
    calc
      _ = barycentric ((realizationProductSimplexIso (Δ[p] : SSet.{u}) q).hom
          ((realizationProductSimplexIso (Δ[p] : SSet.{u}) q).inv z₀)) := rfl
      _ = barycentric z₀ := congrArg barycentric
        (TopCat.inv_hom_id_apply (realizationProductSimplexIso (Δ[p] : SSet.{u}) q) z₀)
      _ = (z, w) := Prod.ext
        ((SimplexCategory.toTopHomeo ⦋p⦌).apply_symm_apply z)
        ((SimplexCategory.toTopHomeo ⦋q⦌).apply_symm_apply w)
  have hg := SimplexGrid.parameter_realization p q y
  rw [hy] at hg
  let z₁ : (|nerve (Codiscrete (Node E))| ⊗ |(Δ[q] : SSet.{u})| : TopCat.{u}) :=
    (CommonReferenceNerve.parameter E N z, (SimplexCategory.toTopHomeo ⦋q⦌).symm w)
  have hz : (SSet.toTop.map (simplexMap E N) ▷ |(Δ[q] : SSet.{u})|) z₀ = z₁ := rfl
  have h : SSet.toTop.map (simplexMap E N ▷ Δ[q]) y =
      (realizationProductSimplexIso (nerve (Codiscrete (Node E))) q).inv z₁ := by
    calc
      _ = ((realizationProductSimplexIso (Δ[p] : SSet.{u}) q).inv ≫
          SSet.toTop.map (simplexMap E N ▷ Δ[q])) z₀ :=
        (CategoryTheory.comp_apply _ _ z₀).symm
      _ = ((SSet.toTop.map (simplexMap E N) ▷ |(Δ[q] : SSet.{u})|) ≫
          (realizationProductSimplexIso (nerve (Codiscrete (Node E))) q).inv) z₀ :=
        ConcreteCategory.congr_hom
          (realizationProductSimplexIso_inv_whisker (simplexMap E N) q) z₀
      _ = (realizationProductSimplexIso (nerve (Codiscrete (Node E))) q).inv
          ((SSet.toTop.map (simplexMap E N) ▷ |(Δ[q] : SSet.{u})|) z₀) :=
        CategoryTheory.comp_apply _ _ z₀
      _ = _ := congrArg
        (realizationProductSimplexIso (nerve (Codiscrete (Node E))) q).inv hz
  calc
    _ = SSet.toTop.map (simplicial E F f)
        (SSet.toTop.map (simplexMap E N ▷ Δ[q]) y) :=
      congrArg (SSet.toTop.map (simplicial E F f)) h.symm
    _ = SSet.toTop.map (simplexMap F (gridNodes E F f N))
        (SSet.toTop.map (SimplexGrid.embedding p q) y) := by
      change (SSet.toTop.map (simplexMap E N ▷ Δ[q]) ≫
        SSet.toTop.map (simplicial E F f)) y =
          (SSet.toTop.map (SimplexGrid.embedding p q) ≫
            SSet.toTop.map (simplexMap F (gridNodes E F f N))) y
      rw [← Functor.map_comp, simplicial_characteristic, Functor.map_comp]
    _ = _ := by
      rw [hg]
      change SSet.toTop.map (simplexMap F (gridNodes E F f N))
        (SSet.toTop.map (SimplexGrid.embedding p q) y) =
          SSet.toTop.map (simplexMap F (gridNodes E F f N))
            ((SimplexCategory.toTopHomeo ⦋SimplexGrid.dimension p q⦌).symm
              (SimplexCategory.toTopHomeo ⦋SimplexGrid.dimension p q⦌
                (SSet.toTop.map (SimplexGrid.embedding p q) y)))
      rw [Homeomorph.symm_apply_apply]

/-- Each entire endpoint is the induced full-node map on the whole source nerve. -/
theorem parameter_vertex (j : Fin (q + 1)) (x : |nerve (Codiscrete (Node E))|) :
    parameter E F f (x, StdSimplex.single j) =
      mapParameter (fun e ↦ f e j) x := by
  obtain ⟨p, N, z, rfl⟩ := exists_parameter E x
  rw [parameter_characteristic, SimplexGrid.parameter_column,
    CommonReferenceNerve.parameter_face, mapParameter_parameter]
  apply congrArg (fun M ↦ CommonReferenceNerve.parameter F M z)
  funext i
  exact gridNodes_index E F f N i j

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.FiniteParameter

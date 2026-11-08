/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.CofiberObjectTrack
public import Colib.KTheory.Waldhausen.GrothendieckComparison.CofiberPrismRealization
public import Colib.Topology.Realization.HomotopyBridge

/-! # The original cofiber prism as a homotopy of its actual triangles

Both time faces retain the entire specified identity-cofiber and original quotient rows.
The actual product-simplex family therefore supplies a simplicial and realized homotopy.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Waldhausen/GrothendieckComparison/CofiberPrismHomotopy.lean`,
all declarations, at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, hypotheses, independent parameters and universes are retained.
Only native namespace, import ownership and line wrapping change.
-/
@[expose] public section
noncomputable section
open SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite Convexity
open MonoidalCategory CartesianMonoidalCategory
open CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- Time zero is the original complete identity-cofiber triangle. -/
theorem cofiberPrismFamily_zero :
    SSet.ι₀ ≫ bisimplexFamily W (cofiberTwoPrism W i q hi hwi hQ)
        (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ) =
      SSet.yonedaEquiv.symm
        (W.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
          (cofiberTwo_identity_square W)) := by
  ext n z
  apply Subtype.ext
  change intervalProjection n.unop ⋙ indexMap z.down ⋙
      (gridRestriction 0 ⋙ cofiberTwoPrism W i q hi hwi hQ) =
    intervalProjection n.unop ⋙ indexMap z.down ⋙
      cofiberTwoDiagram W (𝟙 A) (0 : A ⟶ W.zero) (by simp)
  rw [cofiberTwoPrism_zero]

/-- Time one is the original complete cofiber triangle with its specified inclusion and quotient. -/
theorem cofiberPrismFamily_one :
    SSet.ι₁ ≫ bisimplexFamily W (cofiberTwoPrism W i q hi hwi hQ)
        (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ) =
      SSet.yonedaEquiv.symm (W.cofiberObjectSimplex i q hi hQ) := by
  ext n z
  apply Subtype.ext
  change intervalProjection n.unop ⋙ indexMap z.down ⋙
      (gridRestriction 1 ⋙ cofiberTwoPrism W i q hi hwi hQ) =
    intervalProjection n.unop ⋙ indexMap z.down ⋙
      cofiberTwoDiagram W i q (cofiberTwo_comp_eq_zero W i q hQ)
  rw [cofiberTwoPrism_one]

/-- The genuine product prism is the specified simplicial homotopy of the two original triangles. -/
def cofiberPrismHomotopy :
    SSet.Homotopy
      (SSet.yonedaEquiv.symm
        (W.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
          (cofiberTwo_identity_square W)))
      (SSet.yonedaEquiv.symm (W.cofiberObjectSimplex i q hi hQ)) where
  h := bisimplexFamily W (cofiberTwoPrism W i q hi hwi hQ)
    (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ)
  h₀ := W.cofiberPrismFamily_zero i q hi hwi hQ
  h₁ := W.cofiberPrismFamily_one i q hi hwi hQ
  rel := by ext n z; exact z.1.property.elim

/-- The prescribed barycentric family is exactly the realization of the original prism homotopy. -/
theorem cofiberPrismRealization_homotopy
    (z : StdSimplex ℝ (Fin 3)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z, t) =
      realizationSimplicialHomotopy (W.cofiberPrismHomotopy i q hi hwi hQ)
        (t, (SimplexCategory.toTopHomeo ⦋2⦌).symm z) := by
  let p := (realizationProductSimplexHomeomorph.{max u v} 2 1).symm
    (z, StdSimplex.homeomorphI.symm t)
  have hp := (realizationProductSimplexHomeomorph.{max u v} 2 1).apply_symm_apply
    (z, StdSimplex.homeomorphI.symm t)
  have hp₁ : SSet.toTop.map (fst Δ[2] Δ[1]) p =
      (SimplexCategory.toTopHomeo ⦋2⦌).symm z := by
    apply (SimplexCategory.toTopHomeo ⦋2⦌).injective
    rw [Homeomorph.apply_symm_apply]
    exact congrArg _root_.Prod.fst hp
  have hp₂ : SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (snd Δ[2] Δ[1]) p) = ULift.up t := by
    apply ULift.ext
    change StdSimplex.homeomorphI
      (SimplexCategory.toTopHomeo ⦋1⦌ (SSet.toTop.map (snd Δ[2] Δ[1]) p)) = t
    have ht : SimplexCategory.toTopHomeo ⦋1⦌
        (SSet.toTop.map (snd Δ[2] Δ[1]) p) = StdSimplex.homeomorphI.symm t :=
      congrArg _root_.Prod.snd hp
    rw [ht, Homeomorph.apply_symm_apply]
  have hc : (realizationCylinderIso (Δ[2] : SSet.{max u v})).hom p =
      ((SimplexCategory.toTopHomeo ⦋2⦌).symm z, ULift.up t) :=
    Prod.ext hp₁ hp₂
  have hx : p = (realizationCylinderIso (Δ[2] : SSet.{max u v})).inv
      ((SimplexCategory.toTopHomeo ⦋2⦌).symm z, ULift.up t) := by
    rw [← hc]
    exact (ConcreteCategory.congr_hom
      (realizationCylinderIso (Δ[2] : SSet.{max u v})).hom_inv_id p).symm
  change SSet.toTop.map (bisimplexFamily W (cofiberTwoPrism W i q hi hwi hQ)
      (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ)) p = _
  rw [hx]
  rfl

/-- The three original triangle vertices have their literal constant chosen-zero nerve lines. -/
theorem cofiberPrismHomotopy_vertex_zero (j : Fin 3) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ j) ▷ Δ[1] ≫
        (W.cofiberPrismHomotopy i q hi hwi hQ).h =
      fst Δ[0] Δ[1] ≫
        SSet.yonedaEquiv.symm (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) := by
  ext n z
  apply Subtype.ext
  have hobj : ∀ p,
      (((SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ j) ▷ Δ[1] ≫
        (W.cofiberPrismHomotopy i q hi hwi hQ).h).app n) z).val.obj p = W.zero := by
    intro p
    change (cofiberTwoPrism W i q hi hwi hQ).obj
      (z.2.down.toOrderHom p.1, interval j j le_rfl) = W.zero
    generalize z.2.down.toOrderHom p.1 = k
    fin_cases k <;> fin_cases j <;> rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro p r f
  have hz : IsZero
      ((((SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ j) ▷ Δ[1] ≫
        (W.cofiberPrismHomotopy i q hi hwi hQ).h).app n) z).val.obj p) := by
    rw [hobj p]
    exact W.isZero
  exact hz.eq_of_src _ _

/-- The continuous prism remains at the actual basepoint along every original vertex line. -/
theorem cofiberPrismHomotopy_fixed_vertex (j : Fin 3) (t : unitInterval) :
    realizationSimplicialHomotopy (W.cofiberPrismHomotopy i q hi hwi hQ)
      (t, realizationPoint (X := (Δ[2] : SSet.{max u v}))
        (ULift.up (SimplexCategory.const ⦋0⦌ ⦋2⦌ j))) = W.kBasepoint := by
  exact realizationSimplicialHomotopy_fixed_vertex _ _ _
    (W.cofiberPrismHomotopy_vertex_zero i q hi hwi hQ j) t

end CategoryTheory.Waldhausen.Structure

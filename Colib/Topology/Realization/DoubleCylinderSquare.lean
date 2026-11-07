/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.DoubleHomotopy

/-! # Exact faces and fixed vertices of an original realized double cylinder

The existing double-cylinder isomorphism evaluates a supplied simplicial square.
Its inner time is horizontal and its outer time is vertical. Supplied exact
simplicial face equations recover the original realized homotopies pointwise.
-/
/- Implementation provenance: `Topology/Realization/DoubleCylinderSquare.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original definitions, proofs,
independent parameters and all faces retained in native namespaces. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace SSet
variable {X Y : SSet.{u}} (Q : (X ⊗ Δ[1]) ⊗ Δ[1] ⟶ Y)

/-- Evaluate the supplied square using the original double-cylinder comparison. -/
def realizationDoubleCylinderSquare : C(unitInterval × (unitInterval × |X|), |Y|) where
  toFun z := SSet.toTop.map Q
    ((realizationDoubleCylinderIso X).inv ((z.2.2, ULift.up z.2.1), ULift.up z.1))
  continuous_toFun := (SSet.toTop.map Q).hom.continuous.comp
    ((realizationDoubleCylinderIso X).inv.hom.continuous.comp
      (((continuous_snd.comp continuous_snd).prodMk
        (continuous_uliftUp.comp (continuous_fst.comp continuous_snd))).prodMk
          (continuous_uliftUp.comp continuous_fst)))

/-- The original comparison is exactly the two original inverse cylinder maps. -/
theorem realizationDoubleCylinderSquare_apply (t s : unitInterval) (x : |X|) :
    realizationDoubleCylinderSquare Q (t, (s, x)) =
      SSet.toTop.map Q ((realizationCylinderIso (X ⊗ Δ[1])).inv
        ((realizationCylinderIso X).inv (x, ULift.up s), ULift.up t)) := rfl

variable {f g : X ⟶ Y} (H : SSet.Homotopy f g)

/-- The entire vertical-zero face is the supplied original horizontal homotopy. -/
theorem realizationDoubleCylinderSquare_vertical_zero
    (h : SSet.ι₀ ≫ Q = H.h) (s : unitInterval) (x : |X|) :
    realizationDoubleCylinderSquare Q (0, (s, x)) =
      realizationSimplicialHomotopy H (s, x) := by
  rw [realizationDoubleCylinderSquare_apply]
  change (TopCat.ι₀ ≫ (realizationCylinderIso (X ⊗ Δ[1])).inv ≫ SSet.toTop.map Q)
    ((realizationCylinderIso X).inv (x, ULift.up s)) = _
  rw [← Category.assoc, realizationCylinderIso_inv_zero, ← Functor.map_comp, h]
  rfl

/-- The entire vertical-one face is the supplied original horizontal homotopy. -/
theorem realizationDoubleCylinderSquare_vertical_one
    (h : SSet.ι₁ ≫ Q = H.h) (s : unitInterval) (x : |X|) :
    realizationDoubleCylinderSquare Q (1, (s, x)) =
      realizationSimplicialHomotopy H (s, x) := by
  rw [realizationDoubleCylinderSquare_apply]
  change (TopCat.ι₁ ≫ (realizationCylinderIso (X ⊗ Δ[1])).inv ≫ SSet.toTop.map Q)
    ((realizationCylinderIso X).inv (x, ULift.up s)) = _
  rw [← Category.assoc, realizationCylinderIso_inv_one, ← Functor.map_comp, h]
  rfl

/-- The entire horizontal-zero face is the supplied original vertical homotopy. -/
theorem realizationDoubleCylinderSquare_horizontal_zero
    (h : (SSet.ι₀ ▷ Δ[1]) ≫ Q = H.h) (t : unitInterval) (x : |X|) :
    realizationDoubleCylinderSquare Q (t, (0, x)) =
      realizationSimplicialHomotopy H (t, x) := by
  rw [realizationDoubleCylinderSquare_apply]
  have hi := ConcreteCategory.congr_hom (realizationCylinderIso_inv_zero X) x
  change (realizationCylinderIso X).inv (x, ULift.up 0) = SSet.toTop.map SSet.ι₀ x at hi
  have ho := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (SSet.ι₀ : X ⟶ X ⊗ Δ[1])) (x, ULift.up t)
  change SSet.toTop.map (SSet.ι₀ ▷ Δ[1])
      ((realizationCylinderIso X).inv (x, ULift.up t)) =
    (realizationCylinderIso (X ⊗ Δ[1])).inv (SSet.toTop.map SSet.ι₀ x, ULift.up t) at ho
  rw [hi, ← ho]
  change (SSet.toTop.map (SSet.ι₀ ▷ Δ[1]) ≫ SSet.toTop.map Q)
    ((realizationCylinderIso X).inv (x, ULift.up t)) = _
  rw [← Functor.map_comp, h]
  rfl

/-- The entire horizontal-one face is the supplied original vertical homotopy. -/
theorem realizationDoubleCylinderSquare_horizontal_one
    (h : (SSet.ι₁ ▷ Δ[1]) ≫ Q = H.h) (t : unitInterval) (x : |X|) :
    realizationDoubleCylinderSquare Q (t, (1, x)) =
      realizationSimplicialHomotopy H (t, x) := by
  rw [realizationDoubleCylinderSquare_apply]
  have hi := ConcreteCategory.congr_hom (realizationCylinderIso_inv_one X) x
  change (realizationCylinderIso X).inv (x, ULift.up 1) = SSet.toTop.map SSet.ι₁ x at hi
  have ho := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (SSet.ι₁ : X ⟶ X ⊗ Δ[1])) (x, ULift.up t)
  change SSet.toTop.map (SSet.ι₁ ▷ Δ[1])
      ((realizationCylinderIso X).inv (x, ULift.up t)) =
    (realizationCylinderIso (X ⊗ Δ[1])).inv (SSet.toTop.map SSet.ι₁ x, ULift.up t) at ho
  rw [hi, ← ho]
  change (SSet.toTop.map (SSet.ι₁ ▷ Δ[1]) ≫ SSet.toTop.map Q)
    ((realizationCylinderIso X).inv (x, ULift.up t)) = _
  rw [← Functor.map_comp, h]
  rfl

/-- A whole constant simplicial vertex square fixes both independent continuous times. -/
theorem realizationDoubleCylinderSquare_fixed_vertex
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : ((SSet.yonedaEquiv.symm x ▷ Δ[1]) ▷ Δ[1]) ≫ Q =
      fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫ fst Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm y)
    (t s : unitInterval) :
    realizationDoubleCylinderSquare Q (t, (s, realizationPoint x)) = realizationPoint y := by
  rw [realizationDoubleCylinderSquare_apply]
  let p := (realizationCylinderIso (Δ[0] : SSet.{u})).inv (default, ULift.up s)
  let z := (realizationCylinderIso (Δ[0] ⊗ Δ[1] : SSet.{u})).inv (p, ULift.up t)
  have hi := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (SSet.yonedaEquiv.symm x)) (default, ULift.up s)
  change SSet.toTop.map (SSet.yonedaEquiv.symm x ▷ Δ[1]) p =
    (realizationCylinderIso X).inv (realizationPoint x, ULift.up s) at hi
  have ho := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (SSet.yonedaEquiv.symm x ▷ Δ[1])) (p, ULift.up t)
  change SSet.toTop.map ((SSet.yonedaEquiv.symm x ▷ Δ[1]) ▷ Δ[1]) z =
    (realizationCylinderIso (X ⊗ Δ[1])).inv
      (SSet.toTop.map (SSet.yonedaEquiv.symm x ▷ Δ[1]) p, ULift.up t) at ho
  rw [hi] at ho
  rw [← ho]
  change (SSet.toTop.map ((SSet.yonedaEquiv.symm x ▷ Δ[1]) ▷ Δ[1]) ≫
    SSet.toTop.map Q) z = _
  rw [← Functor.map_comp, h, Functor.map_comp, TopCat.comp_app]
  rw [Functor.map_comp, TopCat.comp_app]
  rw [Subsingleton.elim (SSet.toTop.map (fst Δ[0] Δ[1])
    (SSet.toTop.map (fst (Δ[0] ⊗ Δ[1]) Δ[1]) z)) default]
  rfl

end SSet

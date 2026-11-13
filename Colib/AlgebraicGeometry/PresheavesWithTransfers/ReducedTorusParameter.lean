/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionHI
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus
public import Colib.AlgebraicGeometry.Sites.Smooth.TorusParameter

/-!
# Multiplication by the parameter coordinate on reduced transfer tori

Exterior product with the identity of the native multiplicative group
adds one parameter coordinate to a signed correspondence. Swapping that
coordinate to the first position gives a map into the next torus power.
The actual identity axes of the source land in the corresponding shifted
identity axes. Restriction at parameter one lands in coordinate zero's
identity axis and therefore vanishes on the reduced coefficients.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ

private abbrev torusCor (q : ℕ) : Cor k :=
  Cor.mk (SmoothSite.torusPower Sₖ q)

private abbrev parameterSwapGraph (q : ℕ) :
    Cor.mk (SmoothSite.product (SmoothSite.torusPower Sₖ q) Gₘ) ⟶ torusCor k (q + 1) :=
  (Cor.graphFunctor k).map (SmoothSite.torusPowerParameterSwap Sₖ q)

private def representableLargeMapOfSection {D : Cor k}
    {P : PresheafWithTransfers.{u + 1} k} (s : sections P D) :
    (representableLarge k).obj D ⟶ P :=
  ⟨{
    app X := AddCommGrpCat.ofHom {
      toFun := fun (α : ULift.{u + 1} (X.unop ⟶ D)) ↦ transfer P α.down s
      map_zero' := by
        change transfer P (0 : X.unop ⟶ D) s = 0
        simp
      map_add' α β := by
        change transfer P (α.down + β.down) s =
          transfer P α.down s + transfer P β.down s
        exact ConcreteCategory.congr_hom (transfer_add P α.down β.down) s }
    naturality X Y f := by
      apply AddCommGrpCat.hom_ext
      ext a
      let α : ULift.{u + 1} (X.unop ⟶ D) := a
      change transfer P (f.unop ≫ α.down) s =
        transfer P f.unop (transfer P α.down s)
      simp only [transfer_comp, ConcreteCategory.comp_apply] }⟩

private theorem representableLarge_eq_zero_of_at_identity {D : Cor k}
    {P : PresheafWithTransfers.{u + 1} k} (η : (representableLarge k).obj D ⟶ P)
    (h : η.hom.app (op D) (ULift.up (𝟙 D)) = 0) : η = 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  ext a
  obtain ⟨α⟩ := a
  change η.hom.app X (ULift.up α) = 0
  have hα := NatTrans.naturality_apply η.hom α.op (ULift.up (𝟙 D))
  change η.hom.app X (ULift.up (α ≫ 𝟙 D)) =
    transfer P α (η.hom.app (op D) (ULift.up (𝟙 D))) at hα
  rw [Category.comp_id, h, map_zero] at hα
  exact hα

private theorem toReducedTorus_app_axis (q : ℕ) (i : Fin (q + 1)) {X : Cor k}
    (α : X ⟶ torusCor k q) :
    (toReducedTorus k (q + 1)).hom.app (op X)
      (ULift.up (α ≫ (Cor.graphFunctor k).map (SmoothSite.torusInsertOne Sₖ q i))) = 0 := by
  have hz := congrArg
    (fun f : torusRepresentable k (q + 1 - 1) ⟶ reducedTorus k (q + 1) ↦
      f.hom.app (op X) (ULift.up α)) (torusIdentityAxis_toReducedTorus k (q + 1) i)
  change (toReducedTorus k (q + 1)).hom.app (op X)
    ((torusIdentityAxis k (q + 1) i).hom.app (op X) (ULift.up α)) = 0 at hz
  rw [torusIdentityAxis_app_apply] at hz
  exact hz

/-- Add the parameter coordinate to a torus representable before imposing its identity axes. -/
@[no_expose]
def torusRepresentableParameterProduct (q : ℕ) :
    torusRepresentable k q ⟶ withParameter (reducedTorus k (q + 1)) Gₘ :=
  representableLargeMapOfSection k
    ((toReducedTorus k (q + 1)).hom.app
      (op (Cor.mk (SmoothSite.product (SmoothSite.torusPower Sₖ q) Gₘ)))
      (ULift.up (parameterSwapGraph k q)))

/-- On a signed correspondence the parameter map is exterior product followed
by the graph of the actual coordinate swap and the reduced quotient. -/
theorem torusRepresentableParameterProduct_apply (q : ℕ) (X : Cor k)
    (α : X ⟶ Cor.mk (SmoothSite.torusPower Sₖ q)) :
    (torusRepresentableParameterProduct k q).hom.app (op X) (ULift.up α) =
      (toReducedTorus k (q + 1)).hom.app (op (Cor.mk (SmoothSite.product X.toSmoothSite Gₘ)))
        (ULift.up ((Cor.parameterProduct Gₘ).map α ≫
          (Cor.graphFunctor k).map (SmoothSite.torusPowerParameterSwap Sₖ q))) :=
  reducedTorus_transfer_apply k (q + 1) ((Cor.parameterProduct Gₘ).map α)
    (parameterSwapGraph k q)

private theorem torusIdentityAxis_parameterProduct (q : ℕ) (i : Fin q) :
    torusIdentityAxis k q i ≫ torusRepresentableParameterProduct k q = 0 := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    apply representableLarge_eq_zero_of_at_identity k (D := torusCor k q)
    let D := torusCor k q
    change (torusRepresentableParameterProduct k (q + 1)).hom.app (op D)
      ((torusIdentityAxis k (q + 1) i).hom.app (op D) (ULift.up (𝟙 D))) = 0
    rw [torusIdentityAxis_app_apply, Category.id_comp, torusRepresentableParameterProduct_apply,
      Cor.parameterProduct_graph, ← Functor.map_comp, SmoothSite.torusInsertOne_parameterSwap,
      Functor.map_comp]
    exact toReducedTorus_app_axis k (q + 1) i.succ (parameterSwapGraph k q)

/-- Multiplication by the original parameter coordinate descends to the reduced transfer tori. -/
@[no_expose]
def reducedTorusParameterProduct (q : ℕ) :
    reducedTorus k q ⟶ withParameter (reducedTorus k (q + 1)) Gₘ :=
  reducedTorusDesc k q (torusRepresentableParameterProduct k q)
    (torusIdentityAxis_parameterProduct k q)

@[reassoc (attr := simp)]
theorem toReducedTorus_reducedTorusParameterProduct (q : ℕ) :
    toReducedTorus k q ≫ reducedTorusParameterProduct k q =
      torusRepresentableParameterProduct k q :=
  toReducedTorus_desc k q _ _

/-- The reduced parameter map sends each original signed generator to its
exterior product with the identity parameter and the actual coordinate swap. -/
theorem reducedTorusParameterProduct_apply (q : ℕ) (X : Cor k)
    (α : X ⟶ Cor.mk (SmoothSite.torusPower Sₖ q)) :
    (reducedTorusParameterProduct k q).hom.app (op X)
      ((toReducedTorus k q).hom.app (op X) (ULift.up α)) =
      (toReducedTorus k (q + 1)).hom.app (op (Cor.mk (SmoothSite.product X.toSmoothSite Gₘ)))
        (ULift.up ((Cor.parameterProduct Gₘ).map α ≫
          (Cor.graphFunctor k).map (SmoothSite.torusPowerParameterSwap Sₖ q))) := by
  have h := congrArg
    (fun f : torusRepresentable k q ⟶ withParameter (reducedTorus k (q + 1)) Gₘ ↦
      f.hom.app (op X) (ULift.up α)) (toReducedTorus_reducedTorusParameterProduct k q)
  change (reducedTorusParameterProduct k q).hom.app (op X)
    ((toReducedTorus k q).hom.app (op X) (ULift.up α)) =
    (torusRepresentableParameterProduct k q).hom.app (op X) (ULift.up α) at h
  exact h.trans (torusRepresentableParameterProduct_apply k q X α)

/-- Restriction along the actual unit section of the parameter is zero. -/
@[reassoc (attr := simp)]
theorem reducedTorusParameterProduct_parameterPullback_one (q : ℕ) :
    reducedTorusParameterProduct k q ≫
        parameterPullback (reducedTorus k (q + 1)) (SmoothSite.torusOne Sₖ) = 0 := by
  apply reducedTorus_hom_ext k q
  rw [← Category.assoc, toReducedTorus_reducedTorusParameterProduct, comp_zero]
  apply representableLarge_eq_zero_of_at_identity k (D := torusCor k q)
  let D := torusCor k q
  let F : Cor k ⥤ Cor k := Cor.parameterProduct Gₘ
  let G := Cor.graphFunctor k
  let X := SmoothSite.torusPower Sₖ q
  let E := Cor.mk (SmoothSite.product X (SmoothSite.base Sₖ))
  let g : E ⟶ F.obj D := G.map (SmoothSite.productMap (𝟙 X) (SmoothSite.torusOne Sₖ))
  let b : F.obj D ⟶ torusCor k (q + 1) := parameterSwapGraph k q
  let p : E ⟶ D := G.map (SmoothSite.productFst X (SmoothSite.base Sₖ))
  let evalD (α : F.obj D ⟶ torusCor k (q + 1)) :=
    (toReducedTorus k (q + 1)).hom.app (op (F.obj D)) (ULift.up α)
  have hId : F.map (𝟙 D) ≫ b = b := by rw [F.map_id, Category.id_comp]
  have hSection :
      (torusRepresentableParameterProduct k q).hom.app (op D) (ULift.up (𝟙 D)) = evalD b :=
    (torusRepresentableParameterProduct_apply k q D (𝟙 D)).trans (congrArg evalD hId)
  have hAxis : g ≫ b = p ≫ G.map (SmoothSite.torusInsertOne Sₖ q 0) :=
    ((G.map_comp (SmoothSite.productMap (𝟙 X) (SmoothSite.torusOne Sₖ))
      (SmoothSite.torusPowerParameterSwap Sₖ q)).symm.trans
      (G.congr_map (SmoothSite.torusOne_parameterSwap Sₖ q))).trans
      (G.map_comp (SmoothSite.productFst X (SmoothSite.base Sₖ))
        (SmoothSite.torusInsertOne Sₖ q 0))
  change transfer (reducedTorus k (q + 1)) g
    ((torusRepresentableParameterProduct k q).hom.app (op D) (ULift.up (𝟙 D))) = 0
  rw [hSection]
  calc
    _ = (toReducedTorus k (q + 1)).hom.app (op E) (ULift.up (g ≫ b)) :=
      reducedTorus_transfer_apply k (q + 1) g b
    _ = 0 := (congrArg (fun α : E ⟶ torusCor k (q + 1) ↦
      (toReducedTorus k (q + 1)).hom.app (op E) (ULift.up α)) hAxis).trans
        (toReducedTorus_app_axis k q 0 p)

end AlgebraicGeometry.PresheafWithTransfers

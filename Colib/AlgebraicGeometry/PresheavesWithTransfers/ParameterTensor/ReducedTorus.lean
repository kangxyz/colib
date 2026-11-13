/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.ReducedRepresentable
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusParameter
import Colib.AlgebraicGeometry.PresheavesWithTransfers.EnoughProjectives
import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Products

/-!
# The reduced parameter tensor of a transfer torus

The actual reduced tensor adds the parameter in coordinate zero of the
next torus power. Its coefficient quotient kills the original axes and
the new unit axis. The literal quotient map splits recursively by the
original reduced tensor section.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ
local notation "Bₖ" => SmoothSite.base Sₖ
local notation "D(" q ")" => Cor.mk (SmoothSite.torusPower Sₖ q)
local notation "R" => representableLarge k
local notation "F" => Cor.parameterProduct Gₘ
local notation "L" => parameterTensorFunctor Gₘ
local notation "N" => reducedParameterTensorFunctor k
local notation "a" => parameterTensorAdjunction Gₘ
local notation "b" => reducedParameterTensorAdjunction k

private def parameterSwapIso (q : ℕ) :
    SmoothSite.product (SmoothSite.torusPower Sₖ q) Gₘ ≅
      SmoothSite.torusPower Sₖ (q + 1) where
  hom := SmoothSite.torusPowerParameterSwap Sₖ q
  inv := SmoothSite.productLift
    (SmoothSite.productSnd Gₘ (SmoothSite.torusPower Sₖ q))
    (SmoothSite.productFst Gₘ (SmoothSite.torusPower Sₖ q))
  hom_inv_id := by
    apply SmoothSite.product_hom_ext
    · simp [SmoothSite.torusPowerParameterSwap]
    · simp [SmoothSite.torusPowerParameterSwap]
  inv_hom_id := by
    change _ = 𝟙 (SmoothSite.product Gₘ (SmoothSite.torusPower Sₖ q))
    apply SmoothSite.product_hom_ext
    · simp [SmoothSite.torusPowerParameterSwap]
    · simp [SmoothSite.torusPowerParameterSwap]

private def parameterRepresentableIso (q : ℕ) :
    (L).obj (torusRepresentable k q) ≅ torusRepresentable k (q + 1) :=
  parameterTensorRepresentableIso Gₘ (D(q)) ≪≫
    (R).mapIso ((Cor.graphFunctor k).mapIso (parameterSwapIso k q))

private theorem parameterTensorRepresentableIso_naturality {X Y : Cor k} (f : X ⟶ Y) :
    (L).map ((R).map f) ≫ (parameterTensorRepresentableIso Gₘ Y).hom =
      (parameterTensorRepresentableIso Gₘ X).hom ≫ (R).map ((F).map f) := by
  apply ((a).homEquiv _ _).injective
  rw [(a).homEquiv_naturality_left, (a).homEquiv_naturality_right]
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨α⟩ := x
  let U' := U.unop
  let e := (a).homEquiv ((R).obj X) ((R).obj ((F).obj X))
    (parameterTensorRepresentableIso Gₘ X).hom
  let d := (a).homEquiv ((R).obj Y) ((R).obj ((F).obj Y))
    (parameterTensorRepresentableIso Gₘ Y).hom
  have he : e.hom.app U (ULift.up α) = ULift.up ((F).map α) := by
    unfold e
    rw [Adjunction.homEquiv_unit]
    exact parameterTensorRepresentable_unit_app Gₘ X U' α
  have hd : d.hom.app U (ULift.up (α ≫ f)) = ULift.up ((F).map (α ≫ f)) := by
    unfold d
    rw [Adjunction.homEquiv_unit]
    exact parameterTensorRepresentable_unit_app Gₘ Y U' (α ≫ f)
  change d.hom.app U (ULift.up (α ≫ f)) =
    ((R).map ((F).map f)).hom.app (op ((F).obj U')) (e.hom.app U (ULift.up α))
  rw [he, hd, representableLarge_map_app_apply, Functor.map_comp]

private theorem parameterRepresentableIso_axis (q : ℕ) (i : Fin (q + 1)) :
    (L).map (torusIdentityAxis k (q + 1) i) ≫ (parameterRepresentableIso k (q + 1)).hom =
      (parameterRepresentableIso k q).hom ≫ torusIdentityAxis k (q + 2) i.succ := by
  let G := Cor.graphFunctor k
  let f := SmoothSite.torusInsertOne Sₖ q i
  let j := SmoothSite.torusInsertOne Sₖ (q + 1) i.succ
  let s := SmoothSite.torusPowerParameterSwap Sₖ q
  let t := SmoothSite.torusPowerParameterSwap Sₖ (q + 1)
  let e := (parameterTensorRepresentableIso Gₘ (D(q))).hom
  let f' : D(q) ⟶ D(q + 1) := G.map f
  let e' := (parameterTensorRepresentableIso Gₘ (D(q + 1))).hom
  let a' := (R).map (G.map t)
  let b' := (R).map (G.map s)
  let c' := (R).map (G.map j)
  have hn : (L).map ((R).map f') ≫ e' = e ≫ (R).map ((F).map f') :=
    parameterTensorRepresentableIso_naturality k f'
  have h : (F).map f' ≫ G.map t = G.map s ≫ G.map j := by
    change (F).map (G.map f) ≫ G.map t = _
    rw [Cor.parameterProduct_graph, ← G.map_comp, ← G.map_comp]
    exact G.congr_map (SmoothSite.torusInsertOne_parameterSwap Sₖ q i)
  change (L).map ((R).map f') ≫ (e' ≫ a') = (e ≫ b') ≫ c'
  calc
    _ = ((L).map ((R).map f') ≫ e') ≫ a' := (Category.assoc _ _ _).symm
    _ = (e ≫ (R).map ((F).map f')) ≫ a' := congrArg (· ≫ a') hn
    _ = e ≫ (R).map ((F).map f' ≫ G.map t) :=
      (Category.assoc _ _ _).trans (congrArg (e ≫ ·) ((R).map_comp _ _).symm)
    _ = e ≫ (R).map (G.map s ≫ G.map j) := congrArg (fun m => e ≫ (R).map m) h
    _ = _ := (congrArg (e ≫ ·) ((R).map_comp _ _)).trans (Category.assoc _ _ _).symm

private def parameterBaseRepresentableIso (q : ℕ) :
    (parameterTensorFunctor Bₖ).obj (torusRepresentable k q) ≅ torusRepresentable k q :=
  parameterTensorRepresentableIso Bₖ (D(q)) ≪≫
    (R).mapIso ((Cor.graphFunctor k).mapIso
      (SmoothSite.Contraction.productBaseIso (SmoothSite.torusPower Sₖ q)))

private theorem parameterRepresentableIso_unit (q : ℕ) :
    (torusParameterTensorUnit k).app (torusRepresentable k q) ≫
        (parameterRepresentableIso k q).hom =
      (parameterBaseRepresentableIso k q).hom ≫ torusIdentityAxis k (q + 1) 0 := by
  let G := Cor.graphFunctor k
  let T := SmoothSite.torusPower Sₖ q
  let t := SmoothSite.torusPowerParameterSwap Sₖ q
  let j := SmoothSite.torusInsertOne Sₖ q 0
  let p := SmoothSite.productFst T Bₖ
  let f := SmoothSite.productMap (𝟙 T) (SmoothSite.torusOne Sₖ)
  let e := (parameterTensorRepresentableIso Bₖ (D(q))).hom
  let i := (torusParameterTensorUnit k).app ((R).obj (D(q)))
  let e' := (parameterTensorRepresentableIso Gₘ (D(q))).hom
  let a' := (R).map (G.map t)
  let b' := (R).map (G.map p)
  let c' := (R).map (G.map j)
  have hn : i ≫ e' = e ≫ (R).map (G.map f) :=
    torusParameterTensorUnit_representable k (D(q))
  have h : G.map f ≫ G.map t = G.map p ≫ G.map j := by
    rw [← G.map_comp, ← G.map_comp]
    exact G.congr_map (SmoothSite.torusOne_parameterSwap Sₖ q)
  change i ≫ (e' ≫ a') = (e ≫ b') ≫ c'
  calc
    _ = (i ≫ e') ≫ a' := (Category.assoc _ _ _).symm
    _ = (e ≫ (R).map (G.map f)) ≫ a' := congrArg (· ≫ a') hn
    _ = e ≫ (R).map (G.map f ≫ G.map t) :=
      (Category.assoc _ _ _).trans (congrArg (e ≫ ·) ((R).map_comp _ _).symm)
    _ = e ≫ (R).map (G.map p ≫ G.map j) := congrArg (fun m => e ≫ (R).map m) h
    _ = _ := (congrArg (e ≫ ·) ((R).map_comp _ _)).trans (Category.assoc _ _ _).symm

private theorem toReducedTorus_epi (q : ℕ) : Epi (toReducedTorus k q) where
  left_cancellation _ _ h := reducedTorus_hom_ext k q h

private def parameterProductToKernel (q : ℕ) :
    reducedTorus k q ⟶ contractionKernel (reducedTorus k (q + 1)) :=
  kernel.lift _ (reducedTorusParameterProduct k q)
    (reducedTorusParameterProduct_parameterPullback_one k q)

private def reducedParameterTensorTorusHom (q : ℕ) :
    (N).obj (reducedTorus k q) ⟶ reducedTorus k (q + 1) :=
  ((b).homEquiv _ _).symm (parameterProductToKernel k q)

private def parameterTorusQuotient (q : ℕ) :
    (L).obj (torusRepresentable k q) ⟶ (N).obj (reducedTorus k q) :=
  (L).map (toReducedTorus k q) ≫ (reducedParameterTensorQuotient k).app (reducedTorus k q)

private theorem parameterTorusQuotient_hom (q : ℕ) :
    parameterTorusQuotient k q ≫ reducedParameterTensorTorusHom k q =
      (parameterRepresentableIso k q).hom ≫ toReducedTorus k (q + 1) := by
  let P := reducedTorus k q
  let Q := reducedTorus k (q + 1)
  let f := reducedParameterTensorTorusHom k q
  let j := (reducedParameterTensorQuotient k).app P
  let p := toReducedTorus k q
  let e := (parameterTensorRepresentableIso Gₘ (D(q))).hom
  let s := (Cor.graphFunctor k).map (SmoothSite.torusPowerParameterSwap Sₖ q)
  let t := (R).map s
  have h : (a).homEquiv P Q (j ≫ f) = reducedTorusParameterProduct k q := by
    rw [← reducedParameterTensorAdjunction_homEquiv_ι]
    unfold f reducedParameterTensorTorusHom
    rw [Equiv.apply_symm_apply]
    exact kernel.lift_ι _ _ _
  apply ((a).homEquiv _ _).injective
  change (a).homEquiv _ _ (((L).map p ≫ j) ≫ f) =
    (a).homEquiv _ _ ((e ≫ t) ≫ toReducedTorus k (q + 1))
  rw [Category.assoc, (a).homEquiv_naturality_left, h, Category.assoc,
    (a).homEquiv_naturality_right]
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨α⟩ := x
  let E := (a).homEquiv ((R).obj (D(q))) ((R).obj ((F).obj (D(q)))) e
  have hE : E.hom.app U (ULift.up α) = ULift.up ((F).map α) := by
    unfold E
    rw [Adjunction.homEquiv_unit]
    exact parameterTensorRepresentable_unit_app Gₘ (D(q)) U.unop α
  change (reducedTorusParameterProduct k q).hom.app U (p.hom.app U (ULift.up α)) =
    (toReducedTorus k (q + 1)).hom.app (op ((F).obj U.unop))
      (t.hom.app (op ((F).obj U.unop)) (E.hom.app U (ULift.up α)))
  rw [hE, representableLarge_map_app_apply]
  exact reducedTorusParameterProduct_apply k q U.unop α

private theorem parameterTorusQuotient_axis_succ (q : ℕ) (i : Fin (q + 1)) :
    torusIdentityAxis k (q + 2) i.succ ≫ (parameterRepresentableIso k (q + 1)).inv ≫
      parameterTorusQuotient k (q + 1) = 0 := by
  let e := parameterRepresentableIso k q
  let d := parameterRepresentableIso k (q + 1)
  let f := torusIdentityAxis k (q + 1) i
  let j := torusIdentityAxis k (q + 2) i.succ
  have h : j ≫ d.inv = e.inv ≫ (L).map f := by
    apply (cancel_mono d.hom).1
    rw [Category.assoc, d.inv_hom_id, Category.comp_id,
      Category.assoc, parameterRepresentableIso_axis k q i,
      ← Category.assoc, e.inv_hom_id]
    exact (Category.id_comp j).symm
  rw [← Category.assoc, h]
  change (e.inv ≫ (L).map f) ≫ (L).map (toReducedTorus k (q + 1)) ≫ _ = 0
  rw [Category.assoc, ← (L).map_comp_assoc, torusIdentityAxis_toReducedTorus,
    Functor.map_zero, zero_comp, comp_zero]

private theorem parameterTorusQuotient_axis_zero (q : ℕ) :
    torusIdentityAxis k (q + 1) 0 ≫ (parameterRepresentableIso k q).inv ≫
      parameterTorusQuotient k q = 0 := by
  let e := parameterBaseRepresentableIso k q
  let d := parameterRepresentableIso k q
  let j := torusIdentityAxis k (q + 1) 0
  let i := torusParameterTensorUnit k
  let p := toReducedTorus k q
  let q' := (reducedParameterTensorQuotient k).app (reducedTorus k q)
  have h : j ≫ d.inv = e.inv ≫ i.app (torusRepresentable k q) := by
    apply (cancel_mono d.hom).1
    rw [Category.assoc, d.inv_hom_id, Category.comp_id,
      Category.assoc, parameterRepresentableIso_unit k q,
      ← Category.assoc, e.inv_hom_id]
    exact (Category.id_comp j).symm
  rw [← Category.assoc, h]
  change (e.inv ≫ i.app (torusRepresentable k q)) ≫ (L).map p ≫ q' = 0
  rw [Category.assoc, ← Category.assoc (i.app _) ((L).map p), ← i.naturality p,
    Category.assoc, torusParameterTensorUnit_quotient, comp_zero, comp_zero]

private def reducedParameterTensorTorusInv (q : ℕ) :
    reducedTorus k (q + 1) ⟶ (N).obj (reducedTorus k q) :=
  reducedTorusDesc k (q + 1) ((parameterRepresentableIso k q).inv ≫ parameterTorusQuotient k q)
    (by
      intro i
      cases q with
      | zero =>
        exact Fin.cases (parameterTorusQuotient_axis_zero k 0) (fun j => Fin.elim0 j) i
      | succ q =>
        exact Fin.cases (parameterTorusQuotient_axis_zero k (q + 1))
          (parameterTorusQuotient_axis_succ k q) i)

private theorem toReducedTorus_reducedParameterTensorTorusInv (q : ℕ) :
    toReducedTorus k (q + 1) ≫ reducedParameterTensorTorusInv k q =
      (parameterRepresentableIso k q).inv ≫ parameterTorusQuotient k q :=
  toReducedTorus_desc k (q + 1) _ _

/-- The actual reduced parameter tensor of the reduced weight-`q` torus
is the reduced weight-`q+1` torus with the parameter in coordinate zero. -/
@[no_expose]
def reducedParameterTensorTorusIso (q : ℕ) :
    (N).obj (reducedTorus k q) ≅ reducedTorus k (q + 1) where
  hom := reducedParameterTensorTorusHom k q
  inv := reducedParameterTensorTorusInv k q
  hom_inv_id := by
    let d := parameterRepresentableIso k q
    let p := toReducedTorus k q
    let j := (reducedParameterTensorQuotient k).app (reducedTorus k q)
    let : Epi p := toReducedTorus_epi k q
    let : Epi j := by unfold j; rw [reducedParameterTensorQuotient_app]; infer_instance
    let : Epi (parameterTorusQuotient k q) := inferInstanceAs (Epi ((L).map p ≫ j))
    apply (cancel_epi_id (parameterTorusQuotient k q)).1
    rw [← Category.assoc, parameterTorusQuotient_hom k q, Category.assoc,
      toReducedTorus_reducedParameterTensorTorusInv k q, ← Category.assoc,
      d.hom_inv_id, Category.id_comp]
  inv_hom_id := by
    let d := parameterRepresentableIso k q
    apply reducedTorus_hom_ext k (q + 1)
    rw [← Category.assoc, toReducedTorus_reducedParameterTensorTorusInv k q, Category.assoc,
      parameterTorusQuotient_hom k q, ← Category.assoc, d.inv_hom_id,
      Category.id_comp, Category.comp_id]

/-- Under the actual reduced tensor adjunction, the isomorphism has exactly
the original parameter product as its transpose before unit restriction. -/
@[reassoc]
theorem reducedParameterTensorTorusIso_transpose (q : ℕ) :
    (b).homEquiv _ _ (reducedParameterTensorTorusIso k q).hom ≫
        kernel.ι (torusUnit (reducedTorus k (q + 1))) =
      reducedTorusParameterProduct k q := by
  unfold reducedParameterTensorTorusIso reducedParameterTensorTorusHom
  change (b).homEquiv _ _ (((b).homEquiv _ _).symm (parameterProductToKernel k q)) ≫ _ = _
  rw [Equiv.apply_symm_apply]
  exact kernel.lift_ι _ _ _

private theorem toReducedTorus_succ (q : ℕ) :
    toReducedTorus k (q + 1) =
      (parameterRepresentableIso k q).inv ≫ parameterTorusQuotient k q ≫
        (reducedParameterTensorTorusIso k q).hom := by
  let d := parameterRepresentableIso k q
  change toReducedTorus k (q + 1) = d.inv ≫
    parameterTorusQuotient k q ≫ reducedParameterTensorTorusHom k q
  rw [parameterTorusQuotient_hom, d.inv_hom_id_assoc]

/-- A section of the original torus quotient, obtained by successively
adjoining the actual reduced tensor sections. -/
@[no_expose]
def reducedTorusQuotientSection : (q : ℕ) →
    {s : reducedTorus k q ⟶ torusRepresentable k q // s ≫ toReducedTorus k q = 𝟙 _}
  | 0 => ⟨(reducedTorusZeroIso k).hom, (reducedTorusZeroIso k).hom_inv_id⟩
  | q + 1 => by
    let r := reducedTorusQuotientSection q
    let d := parameterRepresentableIso k q
    let e := reducedParameterTensorTorusIso k q
    let s := (reducedParameterTensorSection k).app (reducedTorus k q)
    refine ⟨e.inv ≫ s ≫ (L).map r.val ≫ d.hom, ?_⟩
    rw [toReducedTorus_succ]
    simp only [Category.assoc]
    have hd : d.hom ≫ (parameterRepresentableIso k q).inv ≫ parameterTorusQuotient k q ≫
        (reducedParameterTensorTorusIso k q).hom =
      parameterTorusQuotient k q ≫ (reducedParameterTensorTorusIso k q).hom :=
      d.hom_inv_id_assoc _
    rw [hd]
    change e.inv ≫ s ≫ (L).map r.val ≫ (L).map (toReducedTorus k q) ≫
      (reducedParameterTensorQuotient k).app (reducedTorus k q) ≫ e.hom = _
    rw [← (L).map_comp_assoc, r.property, (L).map_id, Category.id_comp,
      reducedParameterTensorSection_quotient_assoc, e.inv_hom_id]

instance (q : ℕ) : Projective (reducedTorus k q) := by
  let r := reducedTorusQuotientSection k q
  let e : Retract (reducedTorus k q) (torusRepresentable k q) :=
    ⟨r.val, toReducedTorus k q, r.property⟩
  let : Projective (torusRepresentable k q) :=
    inferInstanceAs (Projective ((representableLarge k).obj (D(q))))
  exact e.projective

end AlgebraicGeometry.PresheafWithTransfers

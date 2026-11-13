/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.ReducedTorus
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusParameter
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation

/-!
# The original cancellation quotient and the reduced torus powers

The target-unit quotient of the weight-`q` torus representable maps
to the reduced weight-`q+1` torus by the actual swap of the new
parameter into coordinate zero. The original exterior-product map
commutes with that quotient on signed correspondence generators.
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
local notation "D(" q ")" => Cor.mk (SmoothSite.torusPower Sₖ q)
local notation "R" => representableLarge k
local notation "F" => Cor.parameterProduct Gₘ

/-- Map the original single-axis target quotient to the quotient by
all axes, with the new unit axis in coordinate zero. -/
def torusCancellationToReducedTorus (q : ℕ) :
    torusCancellationCoefficients k (D(q)) ⟶ reducedTorus k (q + 1) := by
  let G := Cor.graphFunctor k
  let T := SmoothSite.torusPower Sₖ q
  let b := SmoothSite.base Sₖ
  let s := SmoothSite.torusPowerParameterSwap Sₖ q
  let i := SmoothSite.torusInsertOne Sₖ q 0
  let f := SmoothSite.productMap (𝟙 T) (SmoothSite.torusOne Sₖ)
  let p := SmoothSite.productFst T b
  let j : (F).obj (D(q)) ⟶ D(q + 1) := G.map s
  let r := toReducedTorus k (q + 1)
  refine cokernel.desc ((R).map (torusUnitCorrespondence k (D(q)))) ((R).map j ≫ r) ?_
  have h : G.map f ≫ j = G.map p ≫ G.map i := by
    change G.map f ≫ G.map s = _
    rw [← G.map_comp, ← G.map_comp]
    exact G.congr_map (SmoothSite.torusOne_parameterSwap Sₖ q)
  have h₀ : (R).map (G.map f) ≫ (R).map j =
      (R).map (G.map p) ≫ torusIdentityAxis k (q + 1) 0 := by
    change (R).map (G.map f) ≫ (R).map j = (R).map (G.map p) ≫ (R).map (G.map i)
    exact ((R).map_comp _ _).symm.trans (((R).congr_map h).trans ((R).map_comp _ _))
  change (R).map (G.map f) ≫ (R).map j ≫ r = _
  rw [← Category.assoc, h₀, Category.assoc, torusIdentityAxis_toReducedTorus, comp_zero]

/-- The quotient comparison retains postcomposition by the original
parameter swap on every signed correspondence. -/
@[reassoc]
theorem toTorusCancellationCoefficients_torusCancellationToReducedTorus (q : ℕ) :
    toTorusCancellationCoefficients k (D(q)) ≫ torusCancellationToReducedTorus k q =
      (R).map ((Cor.graphFunctor k).map (SmoothSite.torusPowerParameterSwap Sₖ q)) ≫
        toReducedTorus k (q + 1) :=
  cokernel.π_desc _ _ _

/-- The normalized multiplication by the parameter on a reduced torus
is induced by the actual representable cancellation parameter map. -/
@[reassoc]
theorem reducedTorusParameterProduct_quotient (q : ℕ) :
    toReducedTorus k q ≫ reducedTorusParameterProduct k q =
      torusCancellationParameterMap k (D(q)) ≫
        withParameterMap (torusCancellationToReducedTorus k q) Gₘ := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨α⟩ := x
  let X := U.unop
  let j := (Cor.graphFunctor k).map (SmoothSite.torusPowerParameterSwap Sₖ q)
  let p := toReducedTorus k q
  let r := toReducedTorus k (q + 1)
  let Q := toTorusCancellationCoefficients k (D(q))
  let b := torusCancellationToReducedTorus k q
  let a := (F).map α
  change (reducedTorusParameterProduct k q).hom.app U (p.hom.app U (ULift.up α)) =
    b.hom.app (op ((F).obj X))
      ((torusCancellationParameterMap k (D(q))).hom.app U (ULift.up α))
  rw [reducedTorusParameterProduct_apply, torusCancellationParameterMap_app_apply]
  have h := congrArg (fun m : (R).obj ((F).obj (D(q))) ⟶ reducedTorus k (q + 1) =>
    m.hom.app (op ((F).obj X)) (ULift.up a))
      (toTorusCancellationCoefficients_torusCancellationToReducedTorus k q)
  change b.hom.app (op ((F).obj X)) (Q.hom.app (op ((F).obj X)) (ULift.up a)) =
    r.hom.app (op ((F).obj X)) (((R).map j).hom.app (op ((F).obj X)) (ULift.up a)) at h
  rw [representableLarge_map_app_apply] at h
  exact h.symm

private theorem torusCancellationParameterMap_homEquiv (Y : Cor k) :
    (parameterTensorAdjunction Gₘ).homEquiv _ _
      ((parameterTensorRepresentableIso Gₘ Y).hom ≫ toTorusCancellationCoefficients k Y) =
      torusCancellationParameterMap k Y := by
  let a := parameterTensorAdjunction Gₘ
  let e := (parameterTensorRepresentableIso Gₘ Y).hom
  have h : a.homEquiv _ _ e = torusExteriorRepresentableMap k Y := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    obtain ⟨α⟩ := x
    rw [Adjunction.homEquiv_unit]
    exact parameterTensorRepresentable_unit_app Gₘ Y X.unop α
  rw [a.homEquiv_naturality_right, h]
  rfl

/-- The reduced tensor of the literal quotient agrees with the original
target-unit quotient and its parameter swap. -/
@[reassoc]
theorem reducedParameterTensorTorusIso_quotient (q : ℕ) :
    (reducedParameterTensorFunctor k).map (toReducedTorus k q) ≫
        (reducedParameterTensorTorusIso k q).hom =
      (reducedParameterTensorRepresentableIso k (D(q))).hom ≫
        torusCancellationToReducedTorus k q := by
  let B := reducedParameterTensorFunctor k
  let e := reducedParameterTensorAdjunction k
  let L := parameterTensorAdjunction Gₘ
  let P := (R).obj (D(q))
  let Q := reducedTorus k (q + 1)
  let r := toReducedTorus k q
  let f := (reducedParameterTensorTorusIso k q).hom
  let g := (reducedParameterTensorRepresentableIso k (D(q))).hom
  let h := torusCancellationToReducedTorus k q
  let j := kernel.ι (torusUnit Q)
  let u := (reducedParameterTensorQuotient k).app P
  apply (e.homEquiv P Q).injective
  apply (cancel_mono j).1
  change e.homEquiv P Q (B.map r ≫ f) ≫ j = e.homEquiv P Q (g ≫ h) ≫ j
  calc
    _ = r ≫ (e.homEquiv (reducedTorus k q) Q f ≫ j) :=
      (congrArg (· ≫ j) (e.homEquiv_naturality_left r f)).trans (Category.assoc _ _ _)
    _ = r ≫ reducedTorusParameterProduct k q :=
      congrArg (r ≫ ·) (reducedParameterTensorTorusIso_transpose k q)
    _ = torusCancellationParameterMap k (D(q)) ≫ withParameterMap h Gₘ :=
      reducedTorusParameterProduct_quotient k q
    _ = L.homEquiv P Q (u ≫ (g ≫ h)) := by
      rw [← Category.assoc, L.homEquiv_naturality_right]
      have he := reducedParameterTensorRepresentableIso_quotient k (D(q))
      change u ≫ g = (parameterTensorRepresentableIso Gₘ (D(q))).hom ≫
        toTorusCancellationCoefficients k (D(q)) at he
      rw [he]
      have hE := torusCancellationParameterMap_homEquiv k (D(q))
      exact congrArg (· ≫ withParameterMap h Gₘ) hE.symm
    _ = _ := (reducedParameterTensorAdjunction_homEquiv_ι k (g ≫ h)).symm

end AlgebraicGeometry.PresheafWithTransfers

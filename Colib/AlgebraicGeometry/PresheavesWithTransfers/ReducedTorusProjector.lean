/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusCancellation
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Naturality
import Colib.AlgebraicGeometry.PresheavesWithTransfers.YonedaLarge

/-!
# The actual projector for a reduced torus power

The section of the literal axis quotient gives a signed endomorphism
of the original torus by additive Yoneda. The same endomorphism of
the target-unit quotient is the projector whose split image is the
next reduced torus power.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "D(" q ")" => Cor.mk (SmoothSite.torusPower (Spec (CommRingCat.of k)) q)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "R" => representableLarge k
local notation "N" => reducedParameterTensorFunctor k

/-- The signed correspondence inducing the actual reduced torus projector. -/
def reducedTorusProjector (q : ℕ) : D(q) ⟶ D(q) :=
  ((toReducedTorus k q ≫ (reducedTorusQuotientSection k q).val).hom.app (op (D(q)))
    (ULift.up (𝟙 (D(q))))).down

/-- The endomorphism is exactly quotient followed by its original section. -/
theorem representableLarge_map_reducedTorusProjector (q : ℕ) :
    (R).map (reducedTorusProjector k q) =
      toReducedTorus k q ≫ (reducedTorusQuotientSection k q).val := by
  apply (yonedaLargeAddEquiv ((R).obj (D(q))) (D(q))).injective
  let f := reducedTorusProjector k q
  let r := toReducedTorus k q
  let i := (reducedTorusQuotientSection k q).val
  change ((R).map f).hom.app (op (D(q))) (ULift.up (𝟙 (D(q)))) =
    (r ≫ i).hom.app (op (D(q))) (ULift.up (𝟙 (D(q))))
  rw [representableLarge_map_app_apply, Category.id_comp]
  exact ULift.up_down _

/-- On the original target-unit quotients, the coefficient tensor is
natural for a signed morphism of representing objects. -/
@[reassoc]
theorem reducedParameterTensorRepresentableIso_naturality
    {Y Z : Cor k} (f : Y ⟶ Z) :
    (N).map ((R).map f) ≫ (reducedParameterTensorRepresentableIso k Z).hom =
      (reducedParameterTensorRepresentableIso k Y).hom ≫
        torusCancellationCoefficientsMap k f := by
  let i := reducedParameterTensorQuotient k
  let L := parameterTensorFunctor Gₘ
  let F := Cor.parameterProduct Gₘ
  let a := parameterTensorAdjunction Gₘ
  let d := (parameterTensorRepresentableIso Gₘ Y).hom
  let d' := (parameterTensorRepresentableIso Gₘ Z).hom
  let u := (R).map f
  let v := (R).map (F.map f)
  let X := (R).obj Y
  let X' := (R).obj Z
  let e := (reducedParameterTensorRepresentableIso k Y).hom
  let e' := (reducedParameterTensorRepresentableIso k Z).hom
  let p := toTorusCancellationCoefficients k Y
  let p' := toTorusCancellationCoefficients k Z
  let b := torusCancellationCoefficientsMap k f
  let : Epi (i.app X) := by rw [reducedParameterTensorQuotient_app]; infer_instance
  have h : L.map u ≫ d' = d ≫ v := by
    apply (a.homEquiv _ _).injective
    rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right]
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    obtain ⟨α⟩ := x
    let W := U.unop
    let q := a.homEquiv X ((R).obj (F.obj Y)) d
    let q' := a.homEquiv X' ((R).obj (F.obj Z)) d'
    have hq : q.hom.app U (ULift.up α) = ULift.up (F.map α) := by
      unfold q
      rw [Adjunction.homEquiv_unit]
      exact parameterTensorRepresentable_unit_app Gₘ Y W α
    have hq' : q'.hom.app U (ULift.up (α ≫ f)) = ULift.up (F.map (α ≫ f)) := by
      unfold q'
      rw [Adjunction.homEquiv_unit]
      exact parameterTensorRepresentable_unit_app Gₘ Z W (α ≫ f)
    change q'.hom.app U (ULift.up (α ≫ f)) =
      v.hom.app (op (F.obj W)) (q.hom.app U (ULift.up α))
    rw [hq, hq', representableLarge_map_app_apply, F.map_comp]
  apply (cancel_epi (i.app X)).1
  change i.app X ≫ (N).map u ≫ e' = i.app X ≫ e ≫ b
  calc
    _ = L.map u ≫ i.app X' ≫ e' :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ e') (i.naturality u).symm).trans (Category.assoc _ _ _))
    _ = L.map u ≫ d' ≫ p' :=
      congrArg (L.map u ≫ ·) (reducedParameterTensorRepresentableIso_quotient k Z)
    _ = (d ≫ v) ≫ p' :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ p') h)
    _ = d ≫ p ≫ b :=
      (Category.assoc _ _ _).trans
        (congrArg (d ≫ ·) (toTorusCancellationCoefficients_map k f).symm)
    _ = (i.app X ≫ e) ≫ b :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ b) (reducedParameterTensorRepresentableIso_quotient k Y).symm)
    _ = _ := Category.assoc _ _ _

/-- The actual section of the comparison from the target-unit quotient
to the next reduced torus. -/
def reducedTorusCancellationSection (q : ℕ) :
    reducedTorus k (q + 1) ⟶ torusCancellationCoefficients k (D(q)) :=
  (reducedParameterTensorTorusIso k q).inv ≫ (N).map (reducedTorusQuotientSection k q).val ≫
    (reducedParameterTensorRepresentableIso k (D(q))).hom

/-- The comparison is a split quotient with the original reduced tensor section. -/
@[reassoc]
theorem reducedTorusCancellationSection_quotient (q : ℕ) :
    reducedTorusCancellationSection k q ≫ torusCancellationToReducedTorus k q = 𝟙 _ := by
  let d := reducedParameterTensorTorusIso k q
  let e := reducedParameterTensorRepresentableIso k (D(q))
  let i := (reducedTorusQuotientSection k q).val
  let r := toReducedTorus k q
  let f := torusCancellationToReducedTorus k q
  have h := reducedParameterTensorTorusIso_quotient k q
  change (d.inv ≫ (N).map i ≫ e.hom) ≫ f = _
  rw [Category.assoc, Category.assoc, ← h, ← Functor.map_comp_assoc,
    (reducedTorusQuotientSection k q).property]
  exact (congrArg (fun m => d.inv ≫ m ≫ d.hom) ((N).map_id (reducedTorus k q))).trans
    ((congrArg (d.inv ≫ ·) (Category.id_comp d.hom)).trans d.inv_hom_id)

/-- Its complementary projector is obtained by applying the original
target-unit quotient to the actual signed projector on the source. -/
@[reassoc]
theorem torusCancellationToReducedTorus_section (q : ℕ) :
    torusCancellationToReducedTorus k q ≫ reducedTorusCancellationSection k q =
      torusCancellationCoefficientsMap k (reducedTorusProjector k q) := by
  let d := reducedParameterTensorTorusIso k q
  let e := reducedParameterTensorRepresentableIso k (D(q))
  let i := (reducedTorusQuotientSection k q).val
  let r := toReducedTorus k q
  let f := torusCancellationToReducedTorus k q
  let p := reducedTorusProjector k q
  let h := reducedParameterTensorTorusIso_quotient k q
  apply (cancel_epi e.hom).1
  change e.hom ≫ f ≫ d.inv ≫ (N).map i ≫ e.hom =
    e.hom ≫ torusCancellationCoefficientsMap k p
  rw [← Category.assoc e.hom f, ← h, Category.assoc, d.hom_inv_id_assoc,
    ← Functor.map_comp_assoc, ← representableLarge_map_reducedTorusProjector]
  exact reducedParameterTensorRepresentableIso_naturality k p

end AlgebraicGeometry.PresheafWithTransfers

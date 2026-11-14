/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSectionProduct
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphSourceNaturality

/-!
# Ordinary source naturality of the actual section product

The second input is still an unreduced signed
correspondence to Gm; no singular-chain multiplication is asserted.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
open Cor.RelativeGraph
variable (k : Type u) [Field k]
variable {V U : SmoothSite (Spec (CommRingCat.of k))} (f : V ⟶ U)

/-- Ordinary smooth-source pullback acts in both inputs of the real product. -/
theorem reducedTorusSectionProduct_naturality (q : ℕ)
    (s : sections (reducedTorus k q) (Cor.mk U))
    (b : Cor.mk U ⟶ Cor.mk (SmoothSite.multiplicativeGroupObject
      (Spec (CommRingCat.of k)))) :
    transfer (reducedTorus k (q + 1)) ((Cor.graphFunctor k).map f)
      (reducedTorusSectionProduct k U q s b) =
    reducedTorusSectionProduct k V q
      (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f) s)
      ((Cor.graphFunctor k).map f ≫ b) := by
  let P := reducedTorus k (q + 1)
  let G := SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
  let η := reducedTorusParameterProduct k q
  have hn := (NatTrans.naturality_apply η.hom ((Cor.graphFunctor k).map f).op s).symm
  change transfer P ((Cor.parameterProduct G).map ((Cor.graphFunctor k).map f))
      (η.hom.app (op (Cor.mk U)) s) =
    η.hom.app (op (Cor.mk V))
      (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f) s) at hn
  rw [Cor.parameterProduct_graph] at hn
  unfold reducedTorusSectionProduct
  change (transfer P (relativeGraphLift k U G b) ≫
    transfer P ((Cor.graphFunctor k).map f)) (η.hom.app (op (Cor.mk U)) s) = _
  rw [← transfer_comp, relativeGraphLift_graph_comp, transfer_comp]
  change transfer P (relativeGraphLift k V G ((Cor.graphFunctor k).map f ≫ b))
      (transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap f (𝟙 G)))
        (η.hom.app (op (Cor.mk U)) s)) = _
  exact congrArg (fun t => transfer P
    (relativeGraphLift k V G ((Cor.graphFunctor k).map f ≫ b)) t) hn

end AlgebraicGeometry.PresheafWithTransfers

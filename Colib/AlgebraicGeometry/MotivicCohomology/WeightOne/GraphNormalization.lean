/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.Norm

/-!
# Weight-one norm of a torus graph

The actual signed graph of a point of the native Laurent torus maps to
the pullback of the forward coordinate under the geometric reduced norm.
The proof uses the canonical spectrum isomorphism of an integral affine
source and the determinant norm of the linear unit graph.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne

open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers NativeTorusPolynomial

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => multiplicativeGroupObject Sₖ

/-- The reduced signed graph of an actual smooth-site morphism to the torus. -/
def reducedTorusGraphSection {X : SmoothSite Sₖ} (a : X ⟶ Gₘ) :
    (rawReducedTorus k).obj (op X) :=
  (toReducedTorus k 1).hom.app (op (Cor.mk X))
    (ULift.up ((Cor.graphFunctor k).map (a ≫ (torusPowerOneIso Sₖ).inv)))

/-- Pullback of the reduced graph is the reduced graph of the composite. -/
theorem reducedTorusGraphSection_pullback {X Y : SmoothSite Sₖ} (f : X ⟶ Y)
    (a : Y ⟶ Gₘ) :
    (rawReducedTorus k).map f.op (reducedTorusGraphSection k a) =
      reducedTorusGraphSection k (f ≫ a) := by
  let G := Cor.graphFunctor k
  let g : Cor.mk X ⟶ Cor.mk Y := G.map f
  let b : Cor.mk Y ⟶ Cor.mk (torusPower Sₖ 1) := G.map (a ≫ (torusPowerOneIso Sₖ).inv)
  let q (z : Cor.mk X ⟶ Cor.mk (torusPower Sₖ 1)) :=
    (toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up z)
  change transfer (reducedTorus k 1) g
      ((toReducedTorus k 1).hom.app (op (Cor.mk Y)) (ULift.up b)) =
    q (G.map ((f ≫ a) ≫ (torusPowerOneIso Sₖ).inv))
  exact (reducedTorus_transfer_apply k 1 g b).trans
    (congrArg q ((G.map_comp _ _).symm.trans
      (G.congr_map (Category.assoc _ _ _).symm)))

/-- The reduced graph of the basepoint has zero class. -/
theorem reducedTorusGraphSection_torusOne :
    reducedTorusGraphSection k (torusOne Sₖ) = 0 := by
  have ha : torusOne Sₖ ≫ (torusPowerOneIso Sₖ).inv = torusInsertOne Sₖ 0 0 := by
    rw [← torusInsertOne_zero_powerOneIso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let X := Cor.mk (base Sₖ)
  have h := congrArg (fun f : torusRepresentable k 0 ⟶ reducedTorus k 1 =>
    f.hom.app (op X) (ULift.up (𝟙 X))) (torusIdentityAxis_toReducedTorus k 1 0)
  change (toReducedTorus k 1).hom.app (op X)
    ((torusIdentityAxis k 1 0).hom.app (op X) (ULift.up (𝟙 X))) = 0 at h
  rw [torusIdentityAxis_app_apply, Category.id_comp] at h
  unfold reducedTorusGraphSection
  rw [ha]
  exact h

attribute [local instance] AffineSectionCoordinates.sections_isIntegrallyClosed
  AffineSectionCoordinates.sections_isNoetherianRing

set_option maxHeartbeats 400000 in
-- Compare the determinant norm across the canonical affine section isomorphism.
/-- The geometric norm of a reduced graph is pullback of the forward Laurent coordinate. -/
theorem reducedNorm_reducedTorusGraphSection {X : SmoothSite Sₖ}
    [IsAffine X.left] [IsIntegral X.left] (a : X ⟶ Gₘ) :
    (reducedNorm k).app (op X) (reducedTorusGraphSection k a) =
      (largeUnitsPresheaf Sₖ).map a.op
        (ULift.up (Additive.ofMul (multiplicativeGroupBaseChangeCoordinate Sₖ))) := by
  let P := largeUnitsPresheaf Sₖ
  let e := AffineSectionCoordinates.iso X
  let f := AffineSectionCoordinates.structureMap X
  let R := Γ(X.left, ⊤)
  let t := multiplicativeGroupBaseChangeCoordinate Sₖ
  let b := e.hom ≫ a
  let v : Rˣ := Units.map (ΓSpecIso (.of R)).hom.hom.toMonoidHom
    (Units.map b.left.appTop.hom.toMonoidHom t)
  have hv : specGlobalUnit v = Units.map b.left.appTop.hom.toMonoidHom t := by
    apply Units.ext
    exact ConcreteCategory.congr_hom (ΓSpecIso (.of R)).hom_inv_id
      (Units.map b.left.appTop.hom.toMonoidHom t).val
  have hb : smoothUnitPoint f v = b := by
    apply MorphismProperty.Over.Hom.ext
    change (nativeTorusPoint f (specGlobalUnit v)).left = b.left
    rw [hv]
    exact congrArg (fun g => g.left)
      (nativeTorusPoint_recover f (Over.homMk b.left (MorphismProperty.Over.w b)))
  let G := Cor.graphFunctor k
  have hn : powerOneNorm f (G.map (b ≫ (torusPowerOneIso Sₖ).inv)) = Additive.ofMul v := by
    change cycleNorm f (G.map (b ≫ (torusPowerOneIso Sₖ).inv) ≫
      G.map (torusPowerOneIso Sₖ).hom) = _
    rw [← Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id, ← hb,
      graph_smoothUnitPoint, cycleNorm_unitGraph]
  have hP : P.map b.op ≫ (affineSectionIso X P).inv = P.map a.op := by
    change P.map b.op ≫ P.map e.inv.op = _
    rw [← Functor.map_comp, ← op_comp]
    exact P.congr_map (congrArg Quiver.Hom.op (e.inv_hom_id_assoc a))
  unfold reducedTorusGraphSection
  rw [reducedNorm_affine_toReduced]
  let F (z : Cor.mk (AffineSectionCoordinates.obj X) ⟶ Cor.mk (torusPower Sₖ 1)) :=
    (affineSectionIso X P).inv ((specUnitsIso f).inv (ULift.up (powerOneNorm f z)))
  change F (G.map e.hom ≫ G.map (a ≫ (torusPowerOneIso Sₖ).inv)) =
    P.map a.op (ULift.up (Additive.ofMul t))
  have hg : G.map e.hom ≫ G.map (a ≫ (torusPowerOneIso Sₖ).inv) =
      G.map (b ≫ (torusPowerOneIso Sₖ).inv) :=
    (G.map_comp _ _).symm.trans (G.congr_map (Category.assoc _ _ _).symm)
  rw [hg]
  dsimp only [F]
  rw [hn, specUnitsIso_inv_apply]
  let x : P.obj (op Gₘ) := ULift.up (Additive.ofMul t)
  let v' : P.obj (op (AffineSectionCoordinates.obj X)) :=
    ULift.up (Additive.ofMul (specGlobalUnit v))
  have he : v' = P.map b.op x := congrArg (fun z => ULift.up (Additive.ofMul z)) hv
  change (affineSectionIso X P).inv v' = P.map a.op x
  rw [he]
  exact ConcreteCategory.congr_hom hP x

end AlgebraicGeometry.MotivicCohomology.WeightOne

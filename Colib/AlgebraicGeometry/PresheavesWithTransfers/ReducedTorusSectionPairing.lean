/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSectionGenerators
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSectionNaturality

/-!
# Bilinear, ordinary-source-natural reduced torus section pairing

Both arguments are actual reduced torus sections. This is a section-level
pairing, not a singular-chain or derived-tensor product.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
variable (U : SmoothSite (Spec (CommRingCat.of k))) (q : ℕ)

/-- Additivity in the first reduced section survives the actual second quotient. -/
theorem reducedTorusBinarySectionProduct_add_left
    (s t : sections (reducedTorus k q) (Cor.mk U))
    (b : sections (reducedTorus k 1) (Cor.mk U)) :
    reducedTorusBinarySectionProduct k U q (s + t) b =
      reducedTorusBinarySectionProduct k U q s b + reducedTorusBinarySectionProduct k U q t b := by
  obtain ⟨r, rfl⟩ := toReducedTorus_surjective k 1 (Cor.mk U) b
  rw [reducedTorusBinarySectionProduct_generator, reducedTorusBinarySectionProduct_generator,
    reducedTorusBinarySectionProduct_generator]
  exact reducedTorusSectionProduct_add_left k U q s t _

/-- The descended product is zero when its first section is zero. -/
theorem reducedTorusBinarySectionProduct_zero_left
    (b : sections (reducedTorus k 1) (Cor.mk U)) :
    reducedTorusBinarySectionProduct k U q 0 b = 0 := by
  obtain ⟨r, rfl⟩ := toReducedTorus_surjective k 1 (Cor.mk U) b
  rw [reducedTorusBinarySectionProduct_generator]
  change reducedTorusSectionProduct k U q 0 _ = 0
  unfold reducedTorusSectionProduct
  rw [map_zero, map_zero]

/-- The true reduced-section pairing, additive separately in both factors. -/
def reducedTorusSectionPairing : sections (reducedTorus k q) (Cor.mk U) →+
    (sections (reducedTorus k 1) (Cor.mk U) →+
      sections (reducedTorus k (q + 1)) (Cor.mk U)) where
  toFun := reducedTorusBinarySectionProduct k U q
  map_zero' := by
    ext b
    exact reducedTorusBinarySectionProduct_zero_left k U q b
  map_add' s t := by
    ext b
    exact reducedTorusBinarySectionProduct_add_left k U q s t b

/-- Ordinary smooth-source naturality after both actual quotient constructions. -/
theorem reducedTorusSectionPairing_naturality
    {V : SmoothSite (Spec (CommRingCat.of k))} (f : V ⟶ U)
    (s : sections (reducedTorus k q) (Cor.mk U))
    (b : sections (reducedTorus k 1) (Cor.mk U)) :
    transfer (reducedTorus k (q + 1)) ((Cor.graphFunctor k).map f)
        (reducedTorusSectionPairing k U q s b) =
      reducedTorusSectionPairing k V q
        (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f) s)
        (transfer (reducedTorus k 1) ((Cor.graphFunctor k).map f) b) := by
  obtain ⟨⟨r⟩, rfl⟩ := toReducedTorus_surjective k 1 (Cor.mk U) b
  change Cor.mk U ⟶ Cor.mk (SmoothSite.torusPower (Spec (CommRingCat.of k)) 1) at r
  have ht := reducedTorus_transfer_apply k 1 ((Cor.graphFunctor k).map f) r
  calc
    transfer (reducedTorus k (q + 1)) ((Cor.graphFunctor k).map f)
        (reducedTorusBinarySectionProduct k U q s
          ((toReducedTorus k 1).hom.app (op (Cor.mk U)) (ULift.up r))) =
      reducedTorusBinarySectionProduct k V q
        (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f) s)
        ((toReducedTorus k 1).hom.app (op (Cor.mk V))
          (ULift.up ((Cor.graphFunctor k).map f ≫ r))) := by
      rw [reducedTorusBinarySectionProduct_generator, reducedTorusBinarySectionProduct_generator]
      change transfer (reducedTorus k (q + 1)) ((Cor.graphFunctor k).map f)
          (reducedTorusSectionProduct k U q s (r ≫
            (Cor.graphFunctor k).map (SmoothSite.torusPowerOneIso (Spec (CommRingCat.of k))).hom)) =
        reducedTorusSectionProduct k V q
          (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f) s)
          (((Cor.graphFunctor k).map f ≫ r) ≫
            (Cor.graphFunctor k).map (SmoothSite.torusPowerOneIso (Spec (CommRingCat.of k))).hom)
      simpa only [Category.assoc] using reducedTorusSectionProduct_naturality k f q s
        (r ≫ (Cor.graphFunctor k).map (SmoothSite.torusPowerOneIso (Spec (CommRingCat.of k))).hom)
    _ = _ := congrArg (reducedTorusBinarySectionProduct k V q
      (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f) s)) ht.symm

end AlgebraicGeometry.PresheafWithTransfers

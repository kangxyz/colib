/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.GraphNaturality
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.ReducedExact

/-!
# Ordinary coefficient-graph naturality of the actual reduced affine norm

The first torus-power comparison is the existing graph isomorphism. Associativity
of the actual correspondence category transports the proved native torus norm
naturality through it. The existing quotient projection is surjective and natural,
so the actual evaluated cokernel norm is natural. No new quotient or units
transfer is defined. This is source only and is not a global sheaf map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Chow

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
  (f : Spec (.of R) ⟶ Spec (.of k)) (a : R →+* A)
  [Smooth f] [IsSeparated f] [QuasiCompact f]
  [Smooth (Spec.map (CommRingCat.ofHom a) ≫ f)]
  [IsSeparated (Spec.map (CommRingCat.ofHom a) ≫ f)]
  [QuasiCompact (Spec.map (CommRingCat.ofHom a) ≫ f)]
  [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] in
/-- The genuine first-power graph comparison commutes with actual graph precomposition. -/
theorem powerOneCycleEquiv_graph_comp
    (z : Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :
    powerOneCycleEquiv (Spec.map (CommRingCat.ofHom a) ≫ f)
        ((Cor.graphFunctor k).map (coefficientGraph f a) ≫ z) =
      graphRestriction f a (powerOneCycleEquiv f z) := by
  exact Category.assoc ((Cor.graphFunctor k).map (coefficientGraph f a)) z
    ((Cor.graphFunctor k).map (torusPowerOneIso (Spec (.of k))).hom)

omit [IsNoetherianRing R] in
/-- The original first-power determinant norm is natural for arbitrary coefficient graphs. -/
theorem powerOneNorm_graph_comp
    (z : Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :
    powerOneNorm (Spec.map (CommRingCat.ofHom a) ≫ f)
        ((Cor.graphFunctor k).map (coefficientGraph f a) ≫ z) =
      (Units.map a.toMonoidHom).toAdditive (powerOneNorm f z) := by
  change cycleNorm _ (powerOneCycleEquiv _ _) = _
  rw [powerOneCycleEquiv_graph_comp, cycleNorm_graphRestriction]
  rfl

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] in
/-- The existing canonical quotient projection is natural on every actual signed cycle. -/
theorem toReducedTorus_coefficientGraph
    (z : Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :
    transfer (reducedTorus k 1) ((Cor.graphFunctor k).map (coefficientGraph f a))
        ((toReducedTorus k 1).hom.app (op (Cor.mk (mk f))) (ULift.up z)) =
      (toReducedTorus k 1).hom.app
        (op (Cor.mk (mk (Spec.map (CommRingCat.ofHom a) ≫ f))))
        (ULift.up ((Cor.graphFunctor k).map (coefficientGraph f a) ≫ z)) := by
  exact reducedTorus_transfer_apply k 1
    ((Cor.graphFunctor k).map (coefficientGraph f a)) z

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the actual evaluated reduced norm, in the original large universe. -/
theorem reducedNormApp_coefficientGraph
    (z : sections (reducedTorus k 1) (Cor.mk (mk f))) :
    reducedNormApp (Spec.map (CommRingCat.ofHom a) ≫ f)
        (transfer (reducedTorus k 1) ((Cor.graphFunctor k).map (coefficientGraph f a)) z) =
      ULift.up ((Units.map a.toMonoidHom).toAdditive (reducedNormApp f z).down) := by
  obtain ⟨⟨c⟩, rfl⟩ := toReducedTorus_surjective k 1 (Cor.mk (mk f)) z
  rw [toReducedTorus_coefficientGraph f a c,
    reducedNormApp_toReduced, reducedNormApp_toReduced]
  exact congrArg ULift.up (powerOneNorm_graph_comp f a c)

end AlgebraicGeometry.NativeTorusPolynomial

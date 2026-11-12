/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.FramedGraphAction
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.RationalUnitPrincipalAction

/-! # Actual principal polynomial homotopies act trivially on ordinary HI transfers -/

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow
open Scheme Scheme.SmoothSite Scheme.SmoothSite.Contraction
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

local instance {A D : Scheme.{u}} (i : A ⟶ D) [IsOpenImmersion i]
    [IsIntegral A] [IsIntegral D] : IsDominant i :=
  ⟨i.isOpenEmbedding.isOpen_range.dense ⟨i (genericPoint A), Set.mem_range_self _⟩⟩

variable {k : Type u} [Field k]
    (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P)
    (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    {C V W B : Scheme.{u}} (q : C ⟶ X.left) [IsProper q] [IsIntegral C] [IsNoetherian C]
    (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine] [IsIntegral V]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (w : W ⟶ C) [IsOpenImmersion w] [IsIntegral W]
    (b : B ⟶ W) [Nonempty B]
    (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ w))
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
    [IsIntegral (parameterSpace (q ≫ X.hom))]
    [IsNoetherian (parameterSpace (q ≫ X.hom))]
    (g : V ⟶ Y.left) (hg : j ≫ q ≫ X.hom = g ≫ Y.hom)

include hP b hcover hf in
example
    (L : (Cor.graphFunctor k).obj X ⟶ (Cor.graphFunctor k).obj Y)
    (hL : letI := retainedCurve_isNoetherian j
      L.val = noetherianCyclePushforward (retainedCurveMap X.hom Y.hom q j g hg)
        (principalCycle V (j.functionFieldMap (curveRationalFunction w f)))) :
    transfer P L = 0 := by
  exact transfer_principal_polynomial_eq_zero P hP X Y q j w b hcover f hf g hg L hL

end AlgebraicGeometry.PresheafWithTransfers

#print axioms AlgebraicGeometry.PresheafWithTransfers.transfer_principal_polynomial_eq_zero
#print axioms AlgebraicGeometry.PresheafWithTransfers.restriction_eq_of_graph_sub_eq_zsmul_add_principal
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.curveRationalFunction_denseOpen
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.denseOpen_boundary_factor
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.pushforward_principalDivisor_denseUnit
#print axioms AlgebraicGeometry.PresheafWithTransfers.transfer_boundaryNormalized_rationalUnit_eq_zero
#print axioms AlgebraicGeometry.PresheafWithTransfers.transfer_geometric_framed_graph_eq

#print axioms AlgebraicGeometry.PresheafWithTransfers.restriction_eq_of_graph_sub_eq_zsmul_add_boundaryUnit

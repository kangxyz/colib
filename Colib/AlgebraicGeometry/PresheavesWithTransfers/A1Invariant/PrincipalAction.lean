/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.Endpoints
public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointCorrespondence
public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialCylinder

/-! # Actual principal polynomial homotopies act trivially on ordinary HI transfers -/

@[expose] public noncomputable section

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
/-- The independently constructed original principal correspondence acts by zero
on the original ordinary HI coefficient functor. The actual polynomial family
and both endpoint identities are produced, not assumed as a homotopy certificate. -/
@[colib_ref "motivic_source_3df0a472"
  "Motivic/Transfers/Presheaf/Actions/Principal/Family.lean:52-69"
  "adaptation"
  "original HI principal-action argument rebuilt using the actual native polynomial \
  correspondence and both original graph endpoints; no rigidity claim",
  colib_tag "COL-1105"]
theorem transfer_principal_polynomial_eq_zero
    (L : (Cor.graphFunctor k).obj X ⟶ (Cor.graphFunctor k).obj Y)
    (hL : letI := retainedCurve_isNoetherian j
      L.val = noetherianCyclePushforward (retainedCurveMap X.hom Y.hom q j g hg)
        (principalCycle V (j.functionFieldMap (curveRationalFunction w f)))) :
    transfer P L = 0 := by
  let : IsAffine ((𝟭 Scheme).obj X.left) := ‹IsAffine X.left›
  let : IsIntegral ((𝟭 Scheme).obj X.left) := ‹IsIntegral X.left›
  let A : (Cor.graphFunctor k).obj (product X (polynomialAffineLine (.of k))) ⟶
      (Cor.graphFunctor k).obj Y :=
    PrincipalPolynomialFamily.correspondence X.hom Y.hom q j w b hcover f hf g hg
  have H := polynomialCorrespondence_endpointGraph_zero_one X.hom Y.hom q j w b
    hcover f hf g hg
  have H0 : (Cor.graphFunctor k).map (polynomialAffineSection (.of k) X 0) ≫ A = 0 := H.1
  have H1 : (Cor.graphFunctor k).map (polynomialAffineSection (.of k) X 1) ≫ A = L :=
    polynomialCorrespondence_endpointGraph_eq_of_val X.hom Y.hom q j w b hcover f hf g hg L hL
  have HT := transfer_homotopy_endpoints P hP X ((Cor.graphFunctor k).obj Y)
    (nativeCylinderCorrespondence X Y A) 1 0
  rw [graph_nativeAffineSection_comp, graph_nativeAffineSection_comp, H1, H0,
    transfer_zero] at HT
  exact HT

include hP b hcover hf in
/-- A genuine principal correction in an original graph relation disappears on ordinary
HI torsion coefficients. The same original curve, function and outer map are retained. -/
theorem restriction_eq_of_graph_sub_eq_zsmul_add_principal
    (s t : X ⟶ Y)
    (c d L : (Cor.graphFunctor k).obj X ⟶ (Cor.graphFunctor k).obj Y)
    (hL : letI := retainedCurve_isNoetherian j
      L.val = noetherianCyclePushforward (retainedCurveMap X.hom Y.hom q j g hg)
        (principalCycle V (j.functionFieldMap (curveRationalFunction w f))))
    (n : ℤ) (hn : ∀ x : sections P ((Cor.graphFunctor k).obj X), n • x = 0)
    (h : (Cor.graphFunctor k).map s - (Cor.graphFunctor k).map t =
      n • (c - d) + L) :
    ((toPresheaf k).obj P).map s.op = ((toPresheaf k).obj P).map t.op := by
  change transfer P ((Cor.graphFunctor k).map s) = transfer P ((Cor.graphFunctor k).map t)
  apply sub_eq_zero.mp
  rw [← transfer_sub, h, transfer_add, transfer_zsmul,
    transfer_principal_polynomial_eq_zero P hP X Y q j w b hcover f hf g hg L hL, add_zero]
  ext x
  change n • transfer P (c - d) x = 0
  exact hn _

end AlgebraicGeometry.PresheafWithTransfers

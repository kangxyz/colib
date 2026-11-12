/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.DenseOpenBoundaryFactor
public import Colib.AlgebraicGeometry.Correspondences.Principal.RetainedCurveMap
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Actions.PrincipalOrder
public import Colib.AlgebraicGeometry.Correspondences.Moving.PrincipalOrderNoetherianPushforward

/-! # Original boundary-normalized rational-unit actions -/

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
    {C V B : Scheme.{u}} (q : C ⟶ X.left) [IsProper q] [IsIntegral C] [IsNoetherian C]
    (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine] [IsIntegral V]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (i : B ⟶ C) [Nonempty B] (hcover : (Set.range j)ᶜ ⊆ Set.range i)
    [IsIntegral (parameterSpace (q ≫ X.hom))]
    [IsNoetherian (parameterSpace (q ≫ X.hom))]
    (g : V ⟶ Y.left) (hg : j ≫ q ≫ X.hom = g ≫ Y.hom)

include hP i hcover in
/-- The original rational-unit correction supplied by framed moving has zero
HI action. Its full-boundary ordinary unit representative is consumed literally. -/
theorem transfer_boundaryNormalized_rationalUnit_eq_zero
    (F : (rationalFunctions C)ˣ)
    (hF : ∃ (W : DenseOpen C) (u : Γ(C, W.val)ˣ)
      (hBW : ⊤ ≤ i ⁻¹ᵁ W.val),
      Units.map (ofSectionRingHom C W).toMonoidHom u = F ∧
        i.appLE W.val ⊤ hBW u.val = 1)
    (L : (Cor.graphFunctor k).obj X ⟶ (Cor.graphFunctor k).obj Y)
    (hL : letI := retainedCurve_isNoetherian j
      L.val = AlgebraicGeometry.WeilDivisor.pushforwardCycle
        (retainedCurveMap X.hom Y.hom q j g hg)
        (AlgebraicGeometry.principalDivisor V
          (rationalFunctionsUnitsMulEquivOfOpenImmersion j F))) :
    transfer P L = 0 := by
  obtain ⟨W, u, hBW, hu, hu1⟩ := hF
  let : Nonempty W.val := Set.nonempty_coe_sort.mpr W.property.nonempty
  let : IsIntegral W.val.toScheme := inferInstance
  obtain ⟨b, hb, hb1⟩ := denseOpen_boundary_factor W i hBW u.val hu1
  have hc : (Set.range j)ᶜ ⊆ Set.range (b ≫ W.val.ι) := by simpa only [hb] using hcover
  letI := retainedCurve_isNoetherian j
  let hW := Cor.PrincipalOrder.canonical_boundary_cover j W.val b hc
  let m := retainedCurveMap X.hom Y.hom q j g hg
  have hm₁ : m ≫ CategoryTheory.Limits.pullback.fst X.hom Y.hom = j ≫ q :=
    CategoryTheory.Limits.pullback.lift_fst _ _ _
  have hm₂ : m ≫ CategoryTheory.Limits.pullback.snd X.hom Y.hom = g :=
    CategoryTheory.Limits.pullback.lift_snd _ _ _
  have he : L = Cor.PrincipalOrder.correspondence q j W.val hW u.val u.isUnit g hg := by
    apply Subtype.ext
    exact hL.trans (Cor.PrincipalOrder.correspondence_val_eq_pushforward_principalDivisor
      q j g hg W hW u F hu m hm₁ hm₂).symm
  rw [he]
  exact transfer_principalOrder_open_eq_zero P hP X Y q j W.val u.val u.isUnit b hc hb1 g hg

include hP i hcover in
/-- General smooth-base torsion consumer for the actual signed relation produced
by COL-1072. It uses the unchanged rational unit and whole-boundary certificate;
no local coefficient ring, chosen polynomial homotopy, or final rigidity is assumed. -/
theorem restriction_eq_of_graph_sub_eq_zsmul_add_boundaryUnit
    (F : (rationalFunctions C)ˣ)
    (hF : ∃ (W : DenseOpen C) (u : Γ(C, W.val)ˣ)
      (hBW : ⊤ ≤ i ⁻¹ᵁ W.val),
      Units.map (ofSectionRingHom C W).toMonoidHom u = F ∧
        i.appLE W.val ⊤ hBW u.val = 1)
    (L : (Cor.graphFunctor k).obj X ⟶ (Cor.graphFunctor k).obj Y)
    (hL : letI := retainedCurve_isNoetherian j
      L.val = AlgebraicGeometry.WeilDivisor.pushforwardCycle
        (retainedCurveMap X.hom Y.hom q j g hg)
        (AlgebraicGeometry.principalDivisor V
          (rationalFunctionsUnitsMulEquivOfOpenImmersion j F)))
    (s t : X ⟶ Y)
    (c d : (Cor.graphFunctor k).obj X ⟶ (Cor.graphFunctor k).obj Y)
    (n : ℤ) (hn : ∀ x : sections P ((Cor.graphFunctor k).obj X), n • x = 0)
    (h : (Cor.graphFunctor k).map s - (Cor.graphFunctor k).map t = n • (c - d) + L) :
    ((toPresheaf k).obj P).map s.op = ((toPresheaf k).obj P).map t.op := by
  change transfer P ((Cor.graphFunctor k).map s) = transfer P ((Cor.graphFunctor k).map t)
  apply sub_eq_zero.mp
  rw [← transfer_sub, h, transfer_add, transfer_zsmul,
    transfer_boundaryNormalized_rationalUnit_eq_zero P hP X Y q j i hcover g hg F hF L hL,
    add_zero]
  ext x
  change n • transfer P (c - d) x = 0
  exact hn _

end AlgebraicGeometry.PresheafWithTransfers

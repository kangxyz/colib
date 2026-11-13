/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStageSelectedNativeChartOverGround
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SameStageLocalizedRestriction
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SameStageLowerTail
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SameStageLowerIso

/-! # The positive-dimensional rational integral step

This consumes dimension-d polynomial-tail isomorphisms and constructs
preimages for a geometrically integral algebra of transcendence degree d+1
using the actual tuple producer and same-stage restriction. The simultaneous
natural-number induction is assembled in `PolynomialTailSimultaneousInduction`.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry MvPolynomial IntermediateField Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
universe u
namespace QuadraticIncidence.InfinityChart
attribute [local instance] SameStageLocalizedInputs.ring
  SameStageLocalizedInputs.tailSmooth SameStageLocalizedInputs.tailSeparated
  SameStageLocalizedInputs.tailQuasiCompact SameStageLocalizedInputs.affineT

local instance {K : Type u} [Field K] : IsAffine (base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

/-- The producer and S1 create a preimage at positive dimension. No positive
surjectivity hypothesis is inserted among the inputs. -/
theorem exists_rational_integral_original_preimage_of_polynomial_tail_iso
    (K F L B Ω : Type u) [Field K] [Field F] [Field L] [Field Ω] [IsAlgClosed Ω]
    [Infinite L] [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    [Module.Finite K F] [Algebra.IsSeparable K F] [Algebra.IsSeparable F L]
    [CommRing B] [Algebra F B] [Algebra K B] [IsScalarTower K F B]
    [Algebra.Smooth F B] [Algebra.Smooth K B] [IsDomain (L ⊗[F] B)]
    (d : ℕ) (hd : Algebra.trdeg L (L ⊗[F] B) = (d + 1 : ℕ))
    (x : Spec (.of L) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap F B)) =
      Spec.map (CommRingCat.ofHom (algebraMap F L))) (φ : L →+* Ω)
    (P : PresheafWithTransfers.{u + 1} K) (hP : PresheafWithTransfers.IsA1Invariant P)
    (n : ℕ)
    (hn : ∀ (V : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj V)), (n + 1) • z = 0)
    (hnK : IsUnit ((n + 1 : ℕ) : K))
    (hLower : PolynomialTailIsomorphisms K Ω ((PresheafWithTransfers.toPresheaf K).obj P) d)
    (b : ((PresheafWithTransfers.toPresheaf K).obj P).obj
      (op (originalAffineTargetSite K B))) :
    let X := originalAffineTargetSite K B
    let : IsAffine X.left := inferInstanceAs (IsAffine (Spec (.of B)))
    let ξ := Spec.map (CommRingCat.ofHom φ) ≫ x
    let Q := ((PresheafWithTransfers.toPresheaf K).obj P)
    ∃ z : etaleNeighborhoodValue (base (Spec (.of K))) (ξ ≫ X.hom) Q,
      etaleNeighborhoodValuePullback
        (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp) :
          X ⟶ base (Spec (.of K))) (ξ := ξ) rfl Q z =
        toEtaleNeighborhoodValueFromObject X ξ Q b := by
  classical
  obtain ⟨s, hs, _⟩ := exists_finite_tensor_generators F L B
  let g : s → B := fun j => j
  have hg : Algebra.adjoin F (Set.range g) = ⊤ := by
    have hr : Set.range g = (s : Set B) := by
      ext z
      simp [g]
    rwa [hr]
  obtain ⟨t, xE, a, c, re, r, hfin, hsep, hxE, hmark, hre, he, hgood, hnative⟩ :=
    exists_selected_finsetSubfield_rational_native_chart_over_ground
      K F L B g hg d hd x hx
  let E : Type u := adjoin F (t : Set L)
  let : Module.Finite K E := hfin
  let : Algebra.IsSeparable K E := hsep
  let ψ : E →+* Ω := φ.comp (adjoin F (t : Set L)).val.toRingHom
  let G := sameStageLocalizedInputs K F E B hfin hsep g d ⊤ a c (xE default)
    re r xE rfl hre he hgood hnative ψ
  have hGmark : G.originalMark = Spec.map (CommRingCat.ofHom φ) ≫ x := by
    change Spec.map (CommRingCat.ofHom ψ) ≫ xE ≫ finiteStageOriginalTarget F E B = _
    have h := finiteStageChartOriginalTarget_original_mark F E L B
      (adjoin F (t : Set L)).val (𝟙 _) xE xE (Category.comp_id _) x hx hmark
    have h' := congrArg (fun z => Spec.map (CommRingCat.ofHom φ) ≫ z) h
    simpa only [Category.id_comp, Category.comp_id, Category.assoc,
      ψ, CommRingCat.ofHom_comp, Spec.map_comp] using h'
  let : IsAffine (SmoothSite.mk G.tail).left :=
    inferInstanceAs (IsAffine (Spec (.of G.R)))
  let : IsIso (etaleNeighborhoodValuePullback G.tailToBase G.originalMark_base.symm
      ((PresheafWithTransfers.toPresheaf K).obj P)) :=
    sameStageLocalizedInputs_lower_iso K F E B hfin hsep g d ⊤ a c (xE default)
      re r xE rfl hre he hgood hnative ψ hxE
      ((PresheafWithTransfers.toPresheaf K).obj P) hLower
  let target := originalAffineTargetSite K B
  let : IsAffine target.left := inferInstanceAs (IsAffine (Spec (.of B)))
  let Q := ((PresheafWithTransfers.toPresheaf K).obj P)
  let preimage (ξ : Spec (.of Ω) ⟶ Spec (.of B)) : Prop :=
    ∃ z : etaleNeighborhoodValue (base (Spec (.of K))) (ξ ≫ target.hom) Q,
      etaleNeighborhoodValuePullback
        (homMk target.hom (by change target.hom ≫ 𝟙 _ = target.hom; simp) :
          target ⟶ base (Spec (.of K))) (ξ := ξ) rfl Q z =
        toEtaleNeighborhoodValueFromObject target ξ Q b
  have hresult : preimage G.originalMark :=
    G.exists_original_preimage_of_lower_iso P hP n hn hnK b
  exact (congrArg preimage hGmark).mp hresult

end QuadraticIncidence.InfinityChart

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.FiniteBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholePolynomialProducer
public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Complement
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.RelativeLine.SignedCorrection
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.Monic.ZeroSquare
public import Colib.RingTheory.Smooth.IntegrallyClosed

/-! # Whole-line vanishing in degree one from the original monic zero square

The full monic closed fiber and original étale source determine the relative
compactification. Only the coefficient base is shrunk when constructing the
signed correction on the original overlap.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Monic/H1BaseZero.lean`
and `Motivic/Cohomology/A1/LocalVanishing/H1/WholeBaseZero.lean` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open Stacks.Cohomology.FreeYonedaUnivLE

universe w u

namespace AlgebraicGeometry.SheafCohomology

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
open _root_.AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
open PolynomialOpenQuotient PolynomialOpenQuotient.SmoothSite

variable {k R : Type u} [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

set_option maxHeartbeats 650000 in
-- The original square, the refined pencil and its full mark share the same coefficient base.
/-- An ordinary degree-one class that dies on the two original monic-square
legs dies on the whole line over an affine generic base open. -/
theorem exists_monic_h_one_base_open_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (g : R[X]) (hg : g.Monic) {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (p : Y ⟶ lineSite (k := k) (R := R)) [Etale p.left]
    [IsIso (pullback.snd p.left (inclusion g))]
    (e : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).obj
      (op (lineSite (k := k) (R := R))))
    (hA : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).map
      (PolynomialOpenQuotient.SmoothSite.openInclusion g).op e = 0)
    (hY : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).map p.op e = 0) :
    ∃ V : (Spec (.of R)).Opens, IsAffineOpen V ∧ genericPoint (Spec (.of R)) ∈ V ∧
      (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).map
        (SmoothSite.openInclusion (lineSite (k := k) (R := R))
          (polynomialProjection (.of R) ⁻¹ᵁ V)).op e = 0 := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : IsIntegrallyClosed R := Algebra.Smooth.isIntegrallyClosed_of_field k R
  let t := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let : Smooth t := SmoothSite.affineBaseMap_smooth (k := k) (R := R)
  let X := lineSite (k := k) (R := R)
  let : IsAffine (lineSite (k := k) (R := R)).left :=
    inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
  let q := polynomialProjection (.of R)
  have hQt : q ≫ t = X.hom := rfl
  let : SmoothOfRelativeDimension 1 q :=
    Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R
  let a := PolynomialOpenQuotient.SmoothSite.openInclusion (k := k) g
  let : IsAffine (openSite (k := k) g).left := by
    change IsAffineOpen (PolynomialOpenQuotient.principalOpen g)
    exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (Polynomial R)) g
  let : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion (principalOpen g).ι)
  let : IsAffineHom p.left := isAffineHom_of_isAffine _
  let z := PolynomialOpenQuotient.inclusion g
  let s := inv (pullback.snd p.left z) ≫ pullback.fst p.left z
  have H : IsPullback s (𝟙 _) p.left z :=
    (IsPullback.of_hasPullback p.left z).of_iso (asIso (pullback.snd p.left z))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [s]) (by simp) (by simp) (by simp)
  have hs : s ≫ p.left = z := H.w.trans (Category.id_comp _)
  let : IsClosedImmersion s := MorphismProperty.of_isPullback H.flip inferInstance
  have hcomp : Set.range z = (Set.range a.left)ᶜ := by
    change Set.range (PolynomialOpenQuotient.inclusion g) = (Set.range (principalOpen g).ι)ᶜ
    rw [range_inclusion_complement, Scheme.Opens.range_ι]
  have hMarkFin : IsFinite (z ≫ q) := by
    change IsFinite (PolynomialOpenQuotient.inclusion g ≫ polynomialProjection (.of R))
    rw [PolynomialOpenQuotient.inclusion_projection]
    exact PolynomialOpenQuotient.source_finite g hg
  let : IsFinite (coordinateMark R (AdjoinRoot g) (AdjoinRoot.mk g) ≫
      coordinateLineProjection R) := hMarkFin
  let j := RelativeAffineLineEtaleCompactification.inclusion R p.left
  let π := RelativeAffineLineEtaleCompactification.projection R p.left
  let d := infinityInclusion R p.left
  let f := toProjectiveLine R p.left
  let : IsFinite f := toProjectiveLine_finite R p.left k
  let : IsProper π := inferInstanceAs (IsProper
    (f ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))))
  have hj : j ≫ π = p.left ≫ q := inclusion_projection R p.left
  have hsz : (s ≫ j) ≫ π = z ≫ q := by
    rw [Category.assoc, hj, ← Category.assoc, hs]
  let : IsFinite ((s ≫ j) ≫ π) := hsz.symm ▸ hMarkFin
  let : IsFinite (s ≫ j) := IsFinite.of_comp (s ≫ j) π
  let : IsClosedImmersion (s ≫ j) :=
    IsClosedImmersion.of_isPreimmersion _ (s ≫ j).isClosedMap.isClosed_range
  let T := SmoothSite.etalePullback p a
  let α := SmoothSite.etalePullbackFst p a
  let v : T.left ⟶ compactification R p.left := α.left ≫ j
  let : IsAffine T.left := inferInstanceAs (IsAffine (pullback p.left a.left))
  let : IsOpenImmersion α.left := inferInstanceAs (IsOpenImmersion (pullback.fst p.left a.left))
  let : IsOpenImmersion v := inferInstanceAs (IsOpenImmersion (α.left ≫ j))
  have hv : v ≫ π = (α.left ≫ p.left) ≫ q := by
    change (α.left ≫ j) ≫ π = _
    rw [Category.assoc, hj, Category.assoc]
  let : SmoothOfRelativeDimension 1 (v ≫ π) := by
    rw [hv]
    exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _
  have hd : Disjoint (Set.range j) (Set.range d) := by
    rw [range_infinityInclusion R p.left]
    exact disjoint_compl_right
  have ha : Disjoint (Set.range a.left) (Set.range z) := by
    rw [hcomp]
    exact disjoint_compl_right
  have hcover (c : compactification R p.left) :
      c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j) := by
    by_cases hc : c ∈ Set.range j
    · obtain ⟨y, rfl⟩ := hc
      by_cases hy : p.left y ∈ Set.range a.left
      · obtain ⟨w, hw⟩ := (Scheme.Pullback.range_fst p.left a.left).ge hy
        exact Or.inl ⟨w, congrArg j hw⟩
      · have hz : p.left y ∈ Set.range z := by
          rw [hcomp]
          exact hy
        obtain ⟨w, hw⟩ : y ∈ Set.range s := (SmoothSite.range_fst_of_cartesian H).ge hz
        exact Or.inr (Or.inr ⟨w, congrArg j hw⟩)
    · right
      left
      rw [range_infinityInclusion R p.left]
      exact hc
  have hφ : 𝟙 T.left ≫ v = pullback.fst p.left a.left ≫ j := Category.id_comp _
  let : IsProper (d ≫ π) := inferInstance
  obtain ⟨V, hV, hη, hW, hL⟩ := exists_wholePolynomial_base_lifting_of_finite_fiber
    R (AdjoinRoot g) t 1 f j p.left hj a.left (AdjoinRoot.mk g) s hs H d hd ha
    v hcover (𝟙 T.left) hφ (genericPoint (Spec (.of R)))
    (finite_infinity_generic_preimage R p.left k) F.obj hF
  let : IsAffine V.toScheme := hV
  let : IsAffine (parameterOpen q ⊤ V).toScheme := hW
  let G := refinedGraph t q ⊤ V π j p.left hj a.left v (𝟙 T.left) hφ
  let i : refinedTargetSite t V π v ⟶ T :=
    SmoothSite.homMk (sourceBaseOpen π V v).ι (by
      change (sourceBaseOpen π V v).ι ≫ T.hom =
        (sourceBaseMap π V v ≫ compactificationProjection π V) ≫ (V.ι ≫ t)
      have hAmbient : (v ≫ π) ≫ t = T.hom :=
        (congrArg (· ≫ t) hv).trans ((Category.assoc _ _ _).trans
          ((congrArg (α.left ≫ ·) ((Category.assoc _ _ _).trans
            ((congrArg (p.left ≫ ·) hQt).trans (MorphismProperty.Over.w p)))).trans
              (MorphismProperty.Over.w α)))
      have hProjection : (sourceBaseMap π V v ≫ compactificationProjection π V) ≫ V.ι =
          (sourceBaseOpen π V v).ι ≫ (v ≫ π) :=
        (congrArg (· ≫ V.ι) (sourceBaseMap_projection π V v)).trans
          (morphismRestrict_ι (v ≫ π) V)
      exact (congrArg ((sourceBaseOpen π V v).ι ≫ ·) hAmbient.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ t) hProjection.symm).trans (Category.assoc _ _ _))))
  have hi : G.left ≫ i.left = overlapToOriginal q ⊤ V p.left a.left := by
    exact (refinedTargetMap_original q ⊤ V π j p.left hj a.left v (𝟙 T.left) hφ).trans
      (Category.comp_id _)
  refine ⟨V, hV, hη, ?_⟩
  have hz := degreeOne_restriction_zero_of_refined_lifting
    (k := k) (X := X) (Y := Y) (A := openSite (k := k) g) (T := refinedTargetSite t V π v)
    t q hQt p a π j hj V z s H hcomp G i hi F hL e hA hY
  have hOpen : parameterOpen q ⊤ V = q ⁻¹ᵁ V := top_inf_eq (q ⁻¹ᵁ V)
  exact (congrArg (fun O : X.left.Opens =>
    (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).map
      (SmoothSite.openInclusion X O).op e = 0) hOpen).mp hz

attribute [local instance] Algebra.Smooth.away_smooth

/-- The two original coefficient localizations give a whole-line vanishing neighborhood. -/
theorem exists_relative_generic_base_h_one_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (x : (cohomologyPresheaf.{w, u + 1} ((SheafWithTransfers.toSheaf k).obj F) 1).obj
      (op (lineSite (k := k) (R := R)))) :
    ∃ (r : R) (hr : r ≠ 0),
      let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
      ∃ (s : Localization.Away r) (hs : s ≠ 0),
        let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
        ∃ V : (Spec (.of (Localization.Away s))).Opens,
          IsAffineOpen V ∧ genericPoint (Spec (.of (Localization.Away s))) ∈ V ∧
          (cohomologyPresheaf.{w, u + 1}
            ((SheafWithTransfers.toSheaf k).obj F) 1).map
            (SmoothSite.openInclusion (lineSite (k := k) (R := Localization.Away s))
              ((PolynomialLaurent.polynomialProjection (.of (Localization.Away s)) ⁻¹ᵁ V)) ≫
                lineMap (IsScalarTower.toAlgHom k (Localization.Away r) (Localization.Away s)) ≫
                lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op x = 0 := by
  let G := (SheafWithTransfers.toSheaf k).obj F
  let P := cohomologyPresheaf.{w, u + 1} G 1
  obtain ⟨r, hr, f, hf, hx⟩ := exists_relative_monic_open_restriction_eq_zero G 0 x
  let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
  let φ := IsScalarTower.toAlgHom k R (Localization.Away r)
  let x₁ := P.map (lineMap φ).op x
  have hx₁ : P.map (PolynomialOpenQuotient.SmoothSite.openInclusion f).op x₁ = 0 := by
    simpa only [x₁, ← Functor.map_comp_apply, ← op_comp] using hx
  obtain ⟨s, hs, Y, p, hY, hp, hZ, hA, hYx⟩ :=
    exists_relative_monic_positive_zero_square G 0 f hf x₁ hx₁
  let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  let : IsAffine Y.left := hY
  let : Etale p.left := hp
  let : IsIso (pullback.snd p.left
      (inclusion (f.map (algebraMap (Localization.Away r) (Localization.Away s))))) := hZ
  let ψ := IsScalarTower.toAlgHom k (Localization.Away r) (Localization.Away s)
  let x₂ := P.map (lineMap ψ).op x₁
  have hY₂ : P.map p.op x₂ = 0 := by
    simpa only [x₂, ← Functor.map_comp_apply, ← op_comp] using hYx
  obtain ⟨V, hV, hη, hx₂⟩ := exists_monic_h_one_base_open_zero F hF
    (f.map (algebraMap (Localization.Away r) (Localization.Away s))) (hf.map _) p x₂ hA hY₂
  refine ⟨r, hr, s, hs, V, hV, hη, ?_⟩
  let ι := SmoothSite.openInclusion (lineSite (k := k) (R := Localization.Away s))
    (PolynomialLaurent.polynomialProjection (.of (Localization.Away s)) ⁻¹ᵁ V)
  change P.map (ι ≫ lineMap ψ ≫ lineMap φ).op x = 0
  rw [op_comp, Functor.map_comp_apply, op_comp, Functor.map_comp_apply]
  exact hx₂

end AlgebraicGeometry.SheafCohomology

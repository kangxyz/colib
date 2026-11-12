/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.MovingBoundaryFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.MovingBoundarySections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedGeneratedGraph
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.TensorZeroProduct
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# Graph pencil sections on a compactified relative curve

Serre vanishing produces a numerator and a pole with empty zeros on
the whole marked and infinity boundary. The canonical graph coordinate
gives a finite-flat pencil over the affine-line cylinder. The numerator
and pole zero schemes lie in the prescribed open. The first zero ideal
is the product of the graph ideal and the pole zero ideal.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/Moving/OneSided/LocalMoving.lean`
and `Motivic/AlgebraicGeometry/Correspondences/Moving/OneSided/SectionProducer.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors Stacks.Ample
open Stacks.AlgebraicGeometry.RelativeSerreVanishing

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil

/-- The geometric data of the retained graph pencil, before passage to cycles. -/
structure RetainedGraphPencil {k : Type u} [Field k] {S X Y A : Scheme.{u}}
    (t : S ⟶ Spec (.of k)) (q : X ⟶ S) (r : Y ⟶ S)
    (f : X ⟶ Y) (hf : f ≫ r = q) (a : A ⟶ Y) where
  line : (pullback q r).Modules
  poleLine : (pullback q r).Modules
  [line_invertible : AlgebraicGeometry.SheafOfModules.IsInvertible
    (pullback q r).sheaf.obj (pullback q r).ringCatSheaf.property line]
  [poleLine_invertible : AlgebraicGeometry.SheafOfModules.IsInvertible
    (pullback q r).sheaf.obj (pullback q r).ringCatSheaf.property poleLine]
  graphPole : Γ(line, ⊤)
  numerator : Γ(line, ⊤)
  pole : Γ(poleLine, ⊤)
  family_finite : IsFinite (familySource (q ≫ t) (pullback.fst q r) line graphPole numerator)
  family_flat : Flat (familySource (q ≫ t) (pullback.fst q r) line graphPole numerator)
  pole_finite : IsFinite
    ((Stacks.Divisors.zeroScheme (pullback q r) poleLine pole).subschemeι ≫ pullback.fst q r)
  pole_relativeCartier : Stacks.Divisors.IsRelativeEffectiveCartierDivisor (pullback.fst q r)
    (Stacks.Divisors.zeroScheme (pullback q r) poleLine pole)
  graphPole_zero : Stacks.Divisors.zeroScheme (pullback q r) line graphPole =
    relativeGraphIdeal q r f hf * Stacks.Divisors.zeroScheme (pullback q r) poleLine pole
  numerator_support : Set.range
    ((Stacks.Divisors.zeroScheme (pullback q r) line numerator).subschemeι ≫
      pullback.snd q r) ⊆ Set.range a
  pole_support : Set.range
    ((Stacks.Divisors.zeroScheme (pullback q r) poleLine pole).subschemeι ≫
      pullback.snd q r) ⊆ Set.range a

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

local instance {X : Scheme.{u}} (L : X.Modules) [hL : IsInvertibleModule X L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL

private theorem range_retainedZero_target_subset
    {S X Y C A : Scheme.{u}} (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C)
    [IsOpenImmersion j] (a : A ⟶ Y) (I : (pullback q π).IdealSheafData)
    (h : Set.range I.subschemeι ⊆ Set.range (retainedProductInclusion q π (a ≫ j))) :
    Set.range ((I.comap (retainedProductInclusion q π j)).subschemeι ≫
      pullback.snd q (j ≫ π)) ⊆ Set.range a := by
  let g := retainedProductInclusion q π j
  rintro _ ⟨x, rfl⟩
  let x' := (I.comap g).subschemeι x
  have hx : x' ∈ ((I.comap g).support : Set _) := by
    rw [← (I.comap g).range_subschemeι]
    exact ⟨x, rfl⟩
  rw [IdealSheafData.support_comap] at hx
  have hx' : g x' ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hx
  obtain ⟨y, hy⟩ := h hx'
  refine ⟨pullback.snd q ((a ≫ j) ≫ π) y, ?_⟩
  apply j.isOpenEmbedding.injective
  have he := congrArg (fun p => pullback.snd q π p) hy
  change (retainedProductInclusion q π (a ≫ j) ≫ pullback.snd q π) y =
    (g ≫ pullback.snd q π) x' at he
  simpa only [g, retainedProductInclusion_snd, Scheme.Hom.comp_apply] using he

variable {k R : Type u} [Field k] [CommRing R] [IsNoetherianRing R]
  {C Y D Z A : Scheme.{u}}
  (π : C ⟶ Spec (.of R)) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [IsAffine Y] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (t : Spec (.of R) ⟶ Spec (.of k))
  (a : A ⟶ Y)
  (s : Z ⟶ Y) [IsClosedImmersion (s ≫ j)] [IsFinite (s ≫ j ≫ π)]
  (d : D ⟶ C) [IsClosedImmersion d] [IsFinite (d ≫ π)]
  (hd : Disjoint (Set.range j) (Set.range d))
  (hY : ∀ c : C, c ∈ Set.range j ∨ c ∈ Set.range d)
  (hA : ∀ c : C, c ∈ Set.range (a ≫ j) ∨
    c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
  (M : C.Modules) [IsInvertibleModule C M] (hM : IsAmple C M)

local notation "r" => j ≫ π

include hd hY hA hM in
/-- The complete original boundary produces a retained graph pencil around each point. -/
theorem exists_affine_open_retainedGraphPencil (x : Y) :
    ∃ O : Y.affineOpens, x ∈ O.1 ∧
      Nonempty (RetainedGraphPencil t (O.1.ι ≫ r) r O.1.ι rfl a) := by
  let : IsAffineHom r := isAffineHom_of_isAffine r
  let : IsAffineHom (pullback.snd r π) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback r π)
      (inferInstanceAs (IsAffineHom r))
  let L₀ := (Modules.pullback (pullback.snd r π)).obj M
  have hL₀ : IsAmple (pullback r π) L₀ :=
    Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom (pullback.snd r π) M hM
  obtain ⟨O, hx, E, hσ, ⟨eL⟩⟩ := exists_affineMovingBoundaryFrames π j d s hd L₀ x
  let u := O.1.ι
  let q := u ≫ r
  let g := commonToLambda π j u
  let p := pullback.fst q π
  let iD : commonInfinity π j u d ⟶ pullback q π := pullback.fst _ _
  let iZ := commonZeroInclusion π j u s
  let i := commonBoundaryInclusion π j u s d
  let v := retainedProductInclusion q π j
  let w := retainedProductInclusion q π (a ≫ j)
  let G₀ := (compactificationGraph π j).ker
  let F := (Modules.pullback g).obj (divisorSheaf G₀)
  let σ := pullbackGlobalSections g (divisorSheaf G₀) (divisorSheafGlobalSection G₀)
  let L := (Modules.pullback g).obj L₀
  let : IsAffine O.1.toScheme := O.2
  let : IsAffineHom u := isAffineHom_of_isAffine u
  let : IsAffineHom g :=
    MorphismProperty.of_isPullback (commonToLambda_isPullback π j u).flip
      (inferInstanceAs (IsAffineHom u))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian r
  let : IsLocallyNoetherian O.1.toScheme := LocallyOfFiniteType.isLocallyNoetherian u
  let : IsClosedImmersion i := commonBoundary_closed π j u s d hd
  let : IsAffine (pullback q r) := retainedProduct_affine q π j
  let : SmoothOfRelativeDimension 1 (v ≫ p) := retainedProduct_smooth q π j
  have hL : IsAmple (pullback q π) L :=
    Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom g L₀ hL₀
  obtain ⟨N, hN⟩ := exists_eventually_normalized_boundary_sections i p L hL F E
  let T := tensorPowModule (pullback q π) L (N : ℤ)
  let H := tensorModules F T
  let hH : IsInvertibleModule (pullback q π) H :=
    Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf _ F T
  let := hH
  obtain ⟨eT⟩ := exists_tensorPowModule_boundaryFrame i L eL (N : ℤ)
  obtain ⟨aNorm, b, hNorm, ha₁, hb⟩ := hN N le_rfl eT
  let a₁ : Γ(H, ⊤) := aNorm
  let a₀ : Γ(H, ⊤) := tensorSection F T ⊤ σ b
  have hmatch : pullbackGlobalSections iD H a₀ = pullbackGlobalSections iD H a₁ :=
    graphPole_infinity_eq_of_normalization iD iZ F T σ a₁ b E hσ hNorm
  have hInfinityCover : ∀ c : (pullback q π : Scheme.{u}),
      c ∈ Set.range v ∨ c ∈ Set.range iD := by
    intro c
    rcases hY (pullback.snd q π c) with ⟨y, hy⟩ | hD
    · obtain ⟨p, _, hp⟩ := Scheme.exists_preimage_of_isPullback
        (retainedProductInclusion_isPullback q π j) y c hy
      exact Or.inl ⟨p, hp⟩
    · right
      change c ∈ Set.range (pullback.fst (pullback.snd q π) d)
      rwa [Scheme.Pullback.range_fst]
  have hgood : ∀ c : (pullback q π : Scheme.{u}), c ∈ Set.range w ∨ c ∈ Set.range i :=
    commonBoundary_retained_cover π (a ≫ j) j u s d hA
  have haInfinity := zeroScheme_infinity_eq_top_of_boundary_zero iD iZ H a₁ ha₁
  have hbInfinity := zeroScheme_infinity_eq_top_of_boundary_zero iD iZ T b hb
  let HInfinity := (Modules.pullback iD).obj H
  let : IsInvertibleModule (commonInfinity π j u d) HInfinity :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ iD H hH
  let e := frameOfZeroSchemeTop HInfinity (pullbackGlobalSections iD H a₁) haInfinity
  have he : e.hom.app ⊤ (pullbackGlobalSections iD H a₀) =
      (1 : Γ(commonInfinity π j u d, ⊤)) :=
    (congrArg (fun s => e.hom.app ⊤ s) hmatch).trans
      (frameOfZeroSchemeTop_section HInfinity (pullbackGlobalSections iD H a₁) haInfinity)
  obtain ⟨hfin, hflat⟩ := finite_flat_retainedFamily_of_boundary_frame v (q ≫ t) p
    iD H a₀ a₁ hInfinityCover hmatch e.hom he
  obtain ⟨hbp, hbCartier⟩ :=
    finite_relativeCartier_of_boundary_zero iD p v hInfinityCover T b hbInfinity
  have hp : v ≫ p = pullback.fst q r := retainedProductInclusion_fst q π j
  rw [hp] at hfin hflat hbp hbCartier
  let a₀' := pullbackGlobalSections v H a₀
  let a₁' := pullbackGlobalSections v H a₁
  let b' := pullbackGlobalSections v T b
  let N' := (Modules.pullback v).obj H
  let T' := (Modules.pullback v).obj T
  have hF : zeroScheme (pullback q π) F σ = G₀.comap g :=
    (Stacks.Divisors.zeroScheme_pullback g (divisorSheaf G₀)
      (divisorSheafGlobalSection G₀)).trans
      (congrArg (fun I : (pullback r π).IdealSheafData => I.comap g)
        (zeroScheme_canonicalSection G₀))
  have hG : (G₀.comap g).comap v = relativeGraphIdeal q r u rfl :=
    retainedGraph_compactification_ideal π j j u u rfl
  have hprod : zeroScheme (pullback q r) N' a₀' =
      relativeGraphIdeal q r u rfl * zeroScheme (pullback q r) T' b' := by
    let J := zeroScheme (pullback q π) F σ
    let K := zeroScheme (pullback q π) T b
    have hSection : zeroScheme (pullback q π) H a₀ = J * K :=
      zeroScheme_tensorSection_eq_mul F T σ b
    have hPullback := congrArg (fun I : (pullback q π).IdealSheafData => I.comap v) hSection
    have hGraph := (congrArg (fun I : (pullback q π).IdealSheafData => I.comap v) hF).trans hG
    calc
      _ = (zeroScheme (pullback q π) H a₀).comap v :=
        Stacks.Divisors.zeroScheme_pullback v H a₀
      _ = J.comap v * K.comap v := hPullback.trans (Stacks.IdealSheaf.comap_mul J K v)
      _ = _ := congrArg₂ (· * ·) hGraph (Stacks.Divisors.zeroScheme_pullback v T b).symm
  have supportToGood (M : (pullback q π).Modules) [IsInvertibleModule (pullback q π) M]
      (s : Γ(M, ⊤)) (hs : zeroScheme _ ((Modules.pullback i).obj M)
        (pullbackGlobalSections i M s) = ⊤) :
      Set.range ((zeroScheme _ ((Modules.pullback v).obj M)
        (pullbackGlobalSections v M s)).subschemeι ≫ pullback.snd q r) ⊆ Set.range a := by
    have hRange := congrArg
      (fun I : (pullback q r).IdealSheafData => Set.range (I.subschemeι ≫ pullback.snd q r))
      (Stacks.Divisors.zeroScheme_pullback v M s)
    rw [hRange]
    apply range_retainedZero_target_subset q π j a
    exact whole_support_subset_of_boundary_comap_top w i _ hgood
      ((Stacks.Divisors.zeroScheme_pullback i M s).symm.trans hs)
  exact ⟨O, hx, ⟨
    { line := N'
      poleLine := T'
      line_invertible := inferInstance
      poleLine_invertible := inferInstance
      graphPole := a₀'
      numerator := a₁'
      pole := b'
      family_finite := hfin
      family_flat := hflat
      pole_finite := hbp
      pole_relativeCartier := hbCartier
      graphPole_zero := hprod
      numerator_support := supportToGood H a₁ ha₁
      pole_support := supportToGood T b hb }⟩⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil

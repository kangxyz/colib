/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationLocalEquivalences
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationOpenDescent

/-!
# Comparison of closed-pair deformation fibres

The local coordinate and étale comparisons give the two original fibre
equivalences by finite open descent.
-/

public noncomputable section

set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.Contraction
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open Stacks.Deformation Stacks.MoreMorphisms

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

attribute [local irreducible] Cor.graphFunctor transferRepresentable

section RestrictedComparison

variable {Z X : Sm(k)} (i : Z ⟶ X) [IsClosedImmersion i.left]

private theorem isAffineOpen_intersection {X : Sm(k)} {U V : X.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have hh : IsAffineHom (pullback.diagonal X.hom) := inferInstance
  exact (isAffineHom_diagonal_iff (f := X.hom)).mp hh ⊤
    (isAffineOpen_top (Spec (CommRingCat.of k)))
    U (by simp) V (by simp) hU hV

private theorem affineOpen_inclusion_affineHom {X : Sm(k)} {U : X.left.Opens}
    (hU : IsAffineOpen U) : IsAffineHom U.ι := by
  constructor
  intro V hV
  rw [← U.ι.isAffineOpen_iff_of_isOpenImmersion, U.ι.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  exact isAffineOpen_intersection k hU hV

private abbrev IsDeformationChart (U : X.left.Opens) : Prop :=
  (U ≤ closedPairOpen i.left) ∨ ∃ m n : ℕ,
    ∃ (a : (opensFunctor X).obj U ⟶ affineSite k (MvPolynomial (Fin m ⊕ Fin n) k))
      (b : (opensFunctor Z).obj (i.left ⁻¹ᵁ U) ⟶ affineSite k (MvPolynomial (Fin m) k)),
      Etale a.left ∧ IsPullback (restrictClosedImmersion i U).left b.left a.left
        (coordinatePairImmersion k m n).left

private theorem exists_affine_deformation_cover_chart (x : (closedPairDeformation i).left) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ x ∈ deformationBaseOpen i U ∧
      IsDeformationChart k i U := by
  let y := deformationAmbientProjection i x
  by_cases hy : y ∈ Set.range i.left
  · obtain ⟨z, hz⟩ := hy
    obtain ⟨U, hU, hzU, m, n, a, b, ha, h⟩ := exists_affine_open_etale_coordinates k i z
    have hyU : y ∈ U := hz ▸ hzU
    exact ⟨U, hU, hyU, Or.inr ⟨m, n, a, b, ha, h⟩⟩
  · obtain ⟨U, hU, hyU, hle⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ closedPairOpen i.left from hy)
    exact ⟨U, hU, hyU, Or.inl hle⟩

private theorem deformationOpen_le_complement {V : (closedPairDeformation i).left.Opens}
    {U : X.left.Opens} (hV : V ≤ deformationBaseOpen i U) (hU : U ≤ closedPairOpen i.left) :
    V ≤ (closedPairOpenInclusion (deformationSupportInclusion i).left).left.opensRange := by
  change V ≤ (closedPairOpen (deformationSupportInclusion i).left).ι.opensRange
  rw [Scheme.Opens.opensRange_ι]
  intro x hx hx'
  obtain ⟨z, rfl⟩ := hx'
  have h := hU (hV hx)
  apply h
  refine ⟨deformationSpaceToBase (⊥ : Z.left.IdealSheafData) z, ?_⟩
  have eq : (deformationSupportInclusion i).left ≫ deformationAmbientProjection i =
      deformationSpaceToBase (⊥ : Z.left.IdealSheafData) ≫ i.left := by
    change deformationSupportMap i.left ≫ (deformationSpaceToBase _ ≫ _) = _
    rw [deformationSupportMap_toBase_assoc, Scheme.Hom.liftCoborder_ι]
  exact (congrArg (fun f : (deformationSupport Z).left ⟶ X.left => f z) eq).symm

private theorem exists_finite_affine_deformation_cover :
    ∃ (U : (closedPairDeformation i).left → X.left.Opens)
      (s : Finset (closedPairDeformation i).left),
      s.sup (fun x => deformationBaseOpen i (U x)) = ⊤ ∧
        (∀ x, IsAffineOpen (U x)) ∧ ∀ x, IsDeformationChart k i (U x) := by
  classical
  let D := closedPairDeformation i
  have H (x : D.left) := exists_affine_deformation_cover_chart k i x
  choose U hU hx hlocal using H
  let cover (x : D.left) := deformationBaseOpen i (U x)
  have htop : (⨆ x, cover x) = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  let : CompactSpace D.left :=
    QuasiCompact.compactSpace_of_compactSpace (Y := Spec (.of k)) D.hom
  have hcompact : IsCompactElement (⊤ : D.left.Opens) :=
    (TopologicalSpace.Opens.isCompactElement_iff _).mpr isCompact_univ
  obtain ⟨s, hs⟩ := (isCompactElement_iff_exists_le_iSup_of_le_iSup _).mp hcompact
    D.left cover (by rw [htop])
  exact ⟨U, s, top_unique hs, hU, hlocal⟩

private theorem le_of_deformationBaseOpen_le {U V : X.left.Opens}
    (h : deformationBaseOpen i U ≤ deformationBaseOpen i V) : U ≤ V := by
  have hsec : closedPairOneSection i.left ≫ deformationAmbientProjection i = 𝟙 X.left :=
    closedPairOneSection_toAmbient i.left
  have he (W : X.left.Opens) :
      closedPairOneSection i.left ⁻¹ᵁ deformationBaseOpen i W = W := by
    change closedPairOneSection i.left ⁻¹ᵁ (deformationAmbientProjection i ⁻¹ᵁ W) = W
    rw [← Scheme.Hom.comp_preimage, hsec, Scheme.Hom.id_preimage]
  have hpre := (closedPairOneSection i.left).preimage_mono h
  rw [he U, he V] at hpre
  exact hpre

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

private theorem isIso_deformation_mapsOnOpen_of_affineChart (U V : X.left.Opens)
    (hV : IsAffineOpen V) (hVU : V ≤ U) (m n : ℕ)
    (a : (opensFunctor X).obj U ⟶ affineSite k (MvPolynomial (Fin m ⊕ Fin n) k))
    (b : (opensFunctor Z).obj (i.left ⁻¹ᵁ U) ⟶ affineSite k (MvPolynomial (Fin m) k))
    [Etale a.left] (h : IsPullback (restrictClosedImmersion i U).left b.left a.left
      (coordinatePairImmersion k m n).left) :
    IsIso (effectivePairMapOnOpen k (deformationOneSquare i).f₁₃
      (deformationOneSquare i).f₂₄
      (deformationOneSquare i).f₁₂ (deformationOneSquare i).f₃₄ (deformationOneSquare i).fac
      (deformationBaseOpen i V)) ∧
    IsIso (effectivePairMapOnOpen k (deformationZeroSquareOfSmooth i).f₁₃
      (deformationZeroSquareOfSmooth i).f₂₄ (deformationZeroSquareOfSmooth i).f₁₂
      (deformationZeroSquareOfSmooth i).f₃₄ (deformationZeroSquareOfSmooth i).fac
      (deformationBaseOpen i V)) := by
  let α := (opensFunctor X).map (homOfLE hVU)
  let hpre : i.left ⁻¹ᵁ V ≤ i.left ⁻¹ᵁ U := i.left.preimage_mono hVU
  let β := (opensFunctor Z).map (homOfLE hpre)
  let a' := α ≫ a
  let b' := β ≫ b
  let h₀ := restrictClosedImmersion_isPullback i V
  let h₁ := restrictClosedImmersion_isPullback i U
  have hL : IsPullback (restrictClosedImmersion i V).left (β.left ≫ (i.left ⁻¹ᵁ U).ι)
      (α.left ≫ U.ι) i.left := by
    rw [show β.left ≫ (i.left ⁻¹ᵁ U).ι = (i.left ⁻¹ᵁ V).ι from Scheme.homOfLE_ι Z.left hpre]
    rw [show α.left ≫ U.ι = V.ι from Scheme.homOfLE_ι X.left hVU]
    exact h₀
  have he : (restrictClosedImmersion i V).left ≫ α.left =
      β.left ≫ (restrictClosedImmersion i U).left :=
    congrArg (fun f => f.left) (preimageOpenMap_naturality X i hVU).symm
  have h' : IsPullback (restrictClosedImmersion i V).left b'.left a'.left
      (coordinatePairImmersion k m n).left := (hL.of_bot he h₁).paste_vert h
  let : IsAffine ((opensFunctor X).obj V).left := hV
  let : IsAffine ((opensFunctor Z).obj (i.left ⁻¹ᵁ V)).left := hV.preimage i.left
  let : IsOpenImmersion α.left := inferInstanceAs (IsOpenImmersion (X.left.homOfLE hVU))
  let : Etale a'.left := inferInstanceAs (Etale (α.left ≫ a.left))
  obtain ⟨H₁, H₀⟩ := isIso_effectivePairMotiveMap_of_affineEtaleCoordinates k m n
    (restrictClosedImmersion i V) a' b' h'
  let : IsAffineHom V.ι := affineOpen_inclusion_affineHom k hV
  exact ⟨isIso_deformationOneMapOnOpen_of_restriction k i V H₁,
    isIso_deformationZeroMapOnOpen_of_restriction k i V H₀⟩

private theorem isIso_deformation_mapsOnOpen_of_chart (U W : X.left.Opens)
    (hW : IsAffineOpen W) (hWU : W ≤ U) (hU : IsDeformationChart k i U) :
    IsIso (effectivePairMapOnOpen k (deformationOneSquare i).f₁₃
      (deformationOneSquare i).f₂₄ (deformationOneSquare i).f₁₂
      (deformationOneSquare i).f₃₄ (deformationOneSquare i).fac (deformationBaseOpen i W)) ∧
    IsIso (effectivePairMapOnOpen k (deformationZeroSquareOfSmooth i).f₁₃
      (deformationZeroSquareOfSmooth i).f₂₄ (deformationZeroSquareOfSmooth i).f₁₂
      (deformationZeroSquareOfSmooth i).f₃₄ (deformationZeroSquareOfSmooth i).fac
      (deformationBaseOpen i W)) := by
  rcases hU with hOff | ⟨m, n, a, b, ha, h⟩
  · let F := deformationOneSquare i
    let G := deformationZeroSquareOfSmooth i
    let : IsOpenImmersion F.f₁₃.left := inferInstanceAs
      (IsOpenImmersion (closedPairOpenInclusion i.left).left)
    let : IsOpenImmersion F.f₂₄.left := inferInstanceAs
      (IsOpenImmersion (closedPairOpenInclusion (deformationSupportInclusion i).left).left)
    let : IsOpenImmersion G.f₁₃.left := inferInstanceAs
      (IsOpenImmersion (closedPairOpenInclusion (normalBundleZeroSectionOfSmooth i).left).left)
    let : IsOpenImmersion G.f₂₄.left := inferInstanceAs
      (IsOpenImmersion (closedPairOpenInclusion (deformationSupportInclusion i).left).left)
    have hF : IsPullback F.f₁₂.left F.f₁₃.left F.f₂₄.left F.f₃₄.left :=
      (closedPairSquare_isPullback_scheme k (deformationOneSupportSquare i)).flip
    have hG : IsPullback G.f₁₂.left G.f₁₃.left G.f₂₄.left G.f₃₄.left :=
      (closedPairSquare_isPullback_scheme k (deformationZeroSupportSquare i)).flip
    have hR := deformationOpen_le_complement k i
      ((deformationAmbientProjection i).preimage_mono hWU) hOff
    exact ⟨isIso_effectivePairMapOnOpen_of_le_range k
        F.f₁₃ F.f₂₄ F.f₁₂ F.f₃₄ F.fac _ hR hF,
      isIso_effectivePairMapOnOpen_of_le_range k
        G.f₁₃ G.f₂₄ G.f₁₂ G.f₃₄ G.fac _ hR hG⟩
  · let : Etale a.left := ha
    exact isIso_deformation_mapsOnOpen_of_affineChart k i U W hW hWU m n a b h

/-- The original fibre-one and normal-bundle arrows induce isomorphisms on the
actual relative effective motives of every smooth closed pair. -/
theorem isIso_effectivePairMotiveMap_deformationFibres :
    IsIso (effectivePairMotiveMap k (deformationOneSquare i)) ∧
      IsIso (effectivePairMotiveMap k (deformationZeroSquareOfSmooth i)) := by
  classical
  let D := closedPairDeformation i
  obtain ⟨U, s, hcover, hU, hlocal⟩ := exists_finite_affine_deformation_cover k i
  let cover (x : D.left) := deformationBaseOpen i (U x)
  let Q (V : D.left.Opens) := ∃ W : X.left.Opens, IsAffineOpen W ∧ deformationBaseOpen i W = V
  have hQ (V W : D.left.Opens) : Q V → Q W → Q (V ⊓ W) := by
    rintro ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    exact ⟨A ⊓ B, isAffineOpen_intersection k hA hB,
      (deformationAmbientProjection i).preimage_inf⟩
  have hQc (x : D.left) (_ : x ∈ s) : Q (cover x) := ⟨U x, hU x, rfl⟩
  let F := deformationOneSquare i
  let G := deformationZeroSquareOfSmooth i
  let : IsOpenImmersion F.f₁₃.left := inferInstanceAs
    (IsOpenImmersion (closedPairOpenInclusion i.left).left)
  let : IsOpenImmersion F.f₂₄.left := inferInstanceAs
    (IsOpenImmersion (closedPairOpenInclusion (deformationSupportInclusion i).left).left)
  let : IsOpenImmersion G.f₁₃.left := inferInstanceAs
    (IsOpenImmersion (closedPairOpenInclusion (normalBundleZeroSectionOfSmooth i).left).left)
  let : IsOpenImmersion G.f₂₄.left := inferInstanceAs
    (IsOpenImmersion (closedPairOpenInclusion (deformationSupportInclusion i).left).left)
  have hloc (x : D.left) (_ : x ∈ s) (V : D.left.Opens) (hV : V ≤ cover x) (hQV : Q V) :
      IsIso (effectivePairMapOnOpen k F.f₁₃ F.f₂₄ F.f₁₂ F.f₃₄ F.fac V) ∧
        IsIso (effectivePairMapOnOpen k G.f₁₃ G.f₂₄ G.f₁₂ G.f₃₄ G.fac V) := by
    rcases hQV with ⟨W, hW, rfl⟩
    have hw : W ≤ U x := le_of_deformationBaseOpen_le k i hV
    exact isIso_deformation_mapsOnOpen_of_chart k i (U x) W hW hw (hlocal x)
  exact ⟨isIso_effectivePairMap_of_finiteOpenCover_of_inf_closed k
      F.f₁₃ F.f₂₄ F.f₁₂ F.f₃₄ F.fac Q hQ s cover hcover hQc
      (fun x hx V hV hq => (hloc x hx V hV hq).1),
    isIso_effectivePairMap_of_finiteOpenCover_of_inf_closed k
      G.f₁₃ G.f₂₄ G.f₁₂ G.f₃₄ G.fac Q hQ s cover hcover hQc
      (fun x hx V hV hq => (hloc x hx V hV hq).2)⟩

/-- The fibre at one embeds isomorphically on the original relative motives. -/
theorem isIso_effectivePairMotiveMap_deformationOne :
    IsIso (effectivePairMotiveMap k (deformationOneSquare i)) :=
  (isIso_effectivePairMotiveMap_deformationFibres k i).1

/-- The actual normal-bundle fibre embeds isomorphically on relative motives. -/
theorem isIso_effectivePairMotiveMap_deformationZero :
    IsIso (effectivePairMotiveMap k (deformationZeroSquareOfSmooth i)) :=
  (isIso_effectivePairMotiveMap_deformationFibres k i).2

end RestrictedComparison

end AlgebraicGeometry.MotivicHomotopy

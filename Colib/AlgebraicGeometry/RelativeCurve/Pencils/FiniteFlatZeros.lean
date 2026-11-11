/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.ProperQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.LocallyPrincipalFibre
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.LocallyPrincipalPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves

/-!
# Whole finite-flat zero schemes on retained smooth curves

Finiteness of a locally principal closed subscheme of a smooth relative curve forces
the whole closed subscheme to be a relative effective Cartier divisor. The proof uses
Stacks 0B9D over each residue field, where flatness is automatic, followed by Stacks
062Y on the original base. It does not assume that individual irreducible components
are flat over that base.

On a quasi-affine retained curve over an affine base, properness supplies the required
finiteness. A proper compactification need not itself be smooth. Its entire zero scheme
is retained when its whole support lies in the chosen curve open.

This replaces the functional-on-a-line-bundle implementation of
`Motivic/Aglib/AlgebraicGeometry/Modules/Invertible/ZeroLocus/ProperQuasiAffine.lean`,
blob `d958109332516bc77d1a9f27795c547dd6880b6e`, at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, using native ideal sheaves and sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The native comparison with the whole scheme-theoretic fiber preserves its map
to the residue field, not merely its underlying support. -/
@[reassoc]
theorem comapFiberιSubschemeIso_hom_base {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (s : S) :
    (I.comapFiberιSubschemeIso f s).hom ≫ (I.subschemeι ≫ f).fiberToSpecResidueField s =
      (I.comap (f.fiberι s)).subschemeι ≫ f.fiberToSpecResidueField s := by
  change ((I.comapIso (pullback.fst f (S.fromSpecResidueField s))).hom ≫
    (pullbackSymmetry (pullback.fst f (S.fromSpecResidueField s)) I.subschemeι).hom ≫
    (pullbackRightPullbackFstIso f (S.fromSpecResidueField s) I.subschemeι).hom) ≫
      pullback.snd (I.subschemeι ≫ f) (S.fromSpecResidueField s) =
    (I.comap (pullback.fst f (S.fromSpecResidueField s))).subschemeι ≫
      pullback.snd f (S.fromSpecResidueField s)
  rw [Category.assoc, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    pullbackSymmetry_hom_comp_snd_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- A finite locally principal closed subscheme of a smooth relative curve is
a relative effective Cartier divisor. Whole flatness is a conclusion. -/
theorem relativeCartier_of_finite_locallyPrincipal {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] (I : X.IdealSheafData)
    (hI : IsLocallyPrincipal I) [IsFinite (I.subschemeι ≫ f)] :
    IsRelativeEffectiveCartierDivisor f I := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  apply isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres f I hI
  intro s
  have : SmoothOfRelativeDimension 1 (f.fiberToSpecResidueField s) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) inferInstance
  have : IsFinite ((I.comap (f.fiberι s)).subschemeι ≫ f.fiberToSpecResidueField s) := by
    rw [← comapFiberιSubschemeIso_hom_base f I s]
    have : IsFinite ((I.subschemeι ≫ f).fiberToSpecResidueField s) := by
      change IsFinite (pullback.snd (I.subschemeι ≫ f) (S.fromSpecResidueField s))
      exact MorphismProperty.pullback_snd _ _ inferInstance
    infer_instance
  have : Stacks.Morphisms.IsFiniteLocallyFree
      ((I.comap (f.fiberι s)).subschemeι ≫ f.fiberToSpecResidueField s) :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian _).2
      ⟨inferInstance, inferInstance⟩
  exact (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree
    (f.fiberToSpecResidueField s) (I.comap (f.fiberι s))).1

/-- Native sections of invertible modules need no supplied regularity or flatness
once their actual whole zero scheme is finite. -/
theorem relativeCartier_zeroScheme_of_finite {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (a : Γ(L, ⊤)) [IsFinite ((zeroScheme X L a).subschemeι ≫ f)] :
    IsRelativeEffectiveCartierDivisor f (zeroScheme X L a) :=
  relativeCartier_of_finite_locallyPrincipal f _ (isLocallyPrincipal_zeroScheme X L a)

/-- Properness on the unchanged quasi-affine relative curve supplies both finiteness
and the relative Cartier property of the whole locally principal zero scheme. -/
theorem finite_relativeCartier_of_proper {C S : Scheme.{u}} (f : C ⟶ S)
    [SmoothOfRelativeDimension 1 f] [C.IsQuasiAffine] [IsAffine S]
    (I : C.IdealSheafData) (hI : IsLocallyPrincipal I)
    [IsProper (I.subschemeι ≫ f)] :
    IsFinite (I.subschemeι ≫ f) ∧ IsRelativeEffectiveCartierDivisor f I := by
  have : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  have : I.subscheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion I.subschemeι
  have : IsFinite (I.subschemeι ≫ f) :=
    Scheme.isFinite_of_isProper_of_isQuasiAffine (I.subschemeι ≫ f)
  exact ⟨inferInstance, relativeCartier_of_finite_locallyPrincipal f I hI⟩

/-- A whole support contained in an open is not replaced by a smaller divisor:
the projection of its actual pullback to the original closed scheme is an isomorphism. -/
theorem isIso_pullback_snd_of_whole_support {C X : Scheme.{u}} (j : C ⟶ X)
    [IsOpenImmersion j] (I : X.IdealSheafData)
    (h : Set.range I.subschemeι ⊆ Set.range j) :
    IsIso (pullback.snd j I.subschemeι) := by
  have hs : Surjective (pullback.snd j I.subschemeι) := by
    constructor
    intro x
    have hx : x ∈ Set.range (pullback.snd j I.subschemeι) := by
      rw [Scheme.Pullback.range_snd]
      exact h ⟨x, rfl⟩
    exact hx
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hs⟩

/-- A locally principal whole divisor on a proper compactification, entirely supported
in the retained smooth quasi-affine curve, is finite and relative Cartier there.
No smoothness is required of the compactification. -/
theorem finite_relativeCartier_on_open_of_proper {C X S : Scheme.{u}} (p : X ⟶ S)
    [IsProper p] [IsAffine S] (j : C ⟶ X) [IsOpenImmersion j]
    [C.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ p)]
    (I : X.IdealSheafData) (hI : IsLocallyPrincipal I)
    (h : Set.range I.subschemeι ⊆ Set.range j) :
    IsFinite ((I.comap j).subschemeι ≫ (j ≫ p)) ∧
      IsRelativeEffectiveCartierDivisor (j ≫ p) (I.comap j) := by
  have : IsIso (pullback.snd j I.subschemeι) :=
    isIso_pullback_snd_of_whole_support j I h
  have he : (I.comap j).subschemeι ≫ (j ≫ p) =
      (I.comapIso j).hom ≫ pullback.snd j I.subschemeι ≫ I.subschemeι ≫ p := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst I j]
    simp only [Category.assoc, pullback.condition_assoc]
  have : IsProper ((I.comap j).subschemeι ≫ (j ≫ p)) := by
    rw [he]
    infer_instance
  exact finite_relativeCartier_of_proper (j ≫ p) (I.comap j)
    (Stacks.Divisors.isLocallyPrincipal_comap j I hI)

/-- The preceding geometric construction for the actual native zero scheme of a section. -/
theorem finite_relativeCartier_zeroScheme_on_open_of_proper {C X S : Scheme.{u}}
    (p : X ⟶ S) [IsProper p] [IsAffine S] (j : C ⟶ X) [IsOpenImmersion j]
    [C.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ p)] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (a : Γ(L, ⊤)) (h : Set.range (zeroScheme X L a).subschemeι ⊆ Set.range j) :
    IsFinite ((zeroScheme C ((Scheme.Modules.pullback j).obj L)
        (pullbackGlobalSections j L a)).subschemeι ≫ (j ≫ p)) ∧
      IsRelativeEffectiveCartierDivisor (j ≫ p)
        (zeroScheme C ((Scheme.Modules.pullback j).obj L) (pullbackGlobalSections j L a)) := by
  let P : C.IdealSheafData → Prop := fun I =>
    IsFinite (I.subschemeι ≫ (j ≫ p)) ∧ IsRelativeEffectiveCartierDivisor (j ≫ p) I
  have hz : zeroScheme C ((Modules.pullback j).obj L) (pullbackGlobalSections j L a) =
      (zeroScheme X L a).comap j := Stacks.Divisors.zeroScheme_pullback j L a
  exact Eq.mp (congrArg P hz).symm
    (finite_relativeCartier_on_open_of_proper p j (zeroScheme X L a)
      (isLocallyPrincipal_zeroScheme X L a) h)

end AlgebraicGeometry.Scheme.RelativeCurvePencil

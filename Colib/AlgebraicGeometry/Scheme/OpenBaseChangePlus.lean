/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.ModuleOpenBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.OpenSubscheme
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlus
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor

/-! # The bounded-below open base-change mate -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedBaseChangePlus
open Stacks.AlgebraicGeometry.OpenBaseChange
open AlgebraicGeometry.CohomologyScalars (restrictFunctor_preservesInjectiveObjects')

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] HasDerivedCategory.standard

private theorem pullback_open_preservesFiniteLimits {S T : Scheme.{u}}
    (g : T ⟶ S) [IsOpenImmersion g] : PreservesFiniteLimits (Scheme.Modules.pullback g) :=
  preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback g)

local instance {S T : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g] :
    PreservesFiniteLimits (Scheme.Modules.pullback g) := pullback_open_preservesFiniteLimits g

variable {X X' S T : Scheme.{u}} {f : X ⟶ S} {b : X' ⟶ T} {a : X' ⟶ X}
  {g : T ⟶ S} [IsOpenImmersion g] (h : IsPullback a b f g)

variable [IsOpenImmersion a]

private def restrictPushforwardOpenSquare : RestrictPushforwardIso a b f g := by
  let e := h.isoPullback
  let hi : IsOpenImmersion (pullback.fst f g) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip inferInstance
  exact Scheme.Modules.pushforwardOpenBaseChange f g ≪≫
    (@compIsoOfIso _ _ _ _ e (pullback.fst f g) (pullback.snd f g) hi).symm ≪≫
    (Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorCongr h.isoPullback_hom_fst)
      (Scheme.Modules.pushforward (e.hom ≫ pullback.snd f g))) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor a)
      (Scheme.Modules.pushforwardCongr h.isoPullback_hom_snd)

/-- The actual bounded-below mate is induced by the underived pullback–pushforward mate. -/
def openSquareBaseChangePlus :=
  derivedBaseChangePlus (Scheme.Modules.pushforward f)
    (Scheme.Modules.pushforward b)
    (Scheme.Modules.pullback g) (Scheme.Modules.pullback a)
    (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      h.w)


/-- Open base change is invertible at every bounded-below input, without any
perfectness or quasi-coherence premise. -/
theorem isIso_openSquareBaseChangePlus_app
    (K : DerivedCategory.Plus X.Modules) :
    IsIso ((openSquareBaseChangePlus h).app K) := by
  let G := Scheme.Modules.pullback a
  let α := Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans h.w
  have ha : G.PreservesInjectiveObjects := by
    constructor
    intro M hM
    have hr := restrictFunctor_preservesInjectiveObjects' a
    exact Injective.of_iso ((Scheme.Modules.restrictFunctorIsoPullback a).app M)
      (hr.injective_obj hM)
  let : ∀ M : X.Modules, IsIso (α.app M) :=
    isIso_baseChangeNatTrans_app (restrictPushforwardOpenSquare h) h.w
  let : IsIso α := NatIso.isIso_of_isIso_app α
  obtain ⟨n, hn⟩ := K.property
  obtain ⟨C, _, ⟨e⟩⟩ := K.obj.exists_iso_Q_obj_of_isGE n
  obtain ⟨I, i, hi, hI, hIn⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective C n
  let J : CochainComplex.Plus X.Modules := ⟨I, (CochainComplex.plus_iff _ _).2 ⟨n, hIn⟩⟩
  let : ∀ k, Injective (J.obj.X k) := hI
  let L := G.mapCochainComplexPlus.obj J
  let : ∀ k, Injective (L.obj.X k) := fun k ↦ ha.injective_obj (hI k)
  have ht : IsIso ((openSquareBaseChangePlus h).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient X.Modules).obj J))) := by
    apply isIso_derivedBaseChangePlus_app_of_quasiIso _ _ _ _ α J L (𝟙 L)
    · infer_instance
    · let β := NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)
      let : IsIso β := by
        change IsIso ((NatIso.mapHomologicalComplex (asIso α) (ComplexShape.up ℤ)).hom)
        infer_instance
      let : IsIso (β.app J.obj) := inferInstance
      exact Functor.map_isIso _ _
  let eI : DerivedCategory.Qh.obj ((HomotopyCategory.Plus.quotient X.Modules).obj J).obj ≅
      K.obj :=
    (DerivedCategory.quotientCompQhIso X.Modules).app I ≪≫
      (@asIso _ _ _ _ (DerivedCategory.Q.map i)
        ((DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules i).mpr hi)).symm ≪≫ e.symm
  let ep : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient X.Modules).obj J) ≅
      K := DerivedCategory.Plus.ι.preimageIso eI
  let F := (Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
    (Scheme.Modules.pullback g).mapDerivedCategoryPlus
  let H := G.mapDerivedCategoryPlus ⋙
    (Scheme.Modules.pushforward b).rightDerivedFunctorPlus
  let τ : F ⟶ H := openSquareBaseChangePlus h
  change IsIso (τ.app K)
  have he : τ.app K = F.map ep.inv ≫ τ.app _ ≫ H.map ep.hom := by
    rw [← Category.assoc, τ.naturality ep.inv, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      H.map_id, Category.comp_id]
  rw [he]
  infer_instance

/-- The canonical open base-change isomorphism, natural in the input complex. -/
@[expose] def openSquareBaseChangePlusIso :=
  @asIso _ _ _ _ (openSquareBaseChangePlus h)
    ((NatTrans.isIso_iff_isIso_app _).mpr (isIso_openSquareBaseChangePlus_app h))

/-- The natural isomorphism keeps the actual mate on every input. -/
theorem openSquareBaseChangePlusIso_hom_app
    (K : DerivedCategory.Plus X.Modules) :
    (openSquareBaseChangePlusIso h).hom.app K =
      (openSquareBaseChangePlus h).app K := rfl


/-- The actual comparison retains the native underived mate and the right
derived units. This characterizes its forward map on bounded-below complexes. -/
theorem openSquareBaseChangePlusIso_unit
    (K : HomotopyCategory.Plus X.Modules) :
    (Scheme.Modules.pullback g).mapDerivedCategoryPlus.map
        ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith.app
          K) ≫
      (openSquareBaseChangePlusIso h).hom.app (DerivedCategory.Plus.Qh.obj K) =
    (derivedBaseChangePlusAux (Scheme.Modules.pushforward f)
      (Scheme.Modules.pushforward b)
      (Scheme.Modules.pullback g) (Scheme.Modules.pullback a)
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
        h.w)).app K := by
  rw [openSquareBaseChangePlusIso_hom_app]
  exact derivedBaseChangePlus_fac _ _ _ _ _ K

section Pullback

/-- Canonical bounded-below open base change for an arbitrary morphism of schemes. -/
def derivedPushforwardOpenBaseChangePlus {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [IsOpenImmersion g] :=
  letI : IsOpenImmersion (Limits.pullback.fst f g) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip inferInstance
  openSquareBaseChangePlusIso (IsPullback.of_hasPullback f g)

end Pullback

end AlgebraicGeometry.Scheme.Modules

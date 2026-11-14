/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.FlatBaseChangePlus
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.FlatBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNatTransDevissage
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlusOfDerived

/-! # The flat bounded-below base-change mate on perfect inputs -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.FlatBaseChangeDerived
open Stacks.Cohomology.DerivedBaseChangePlus
open RingedSpaceModuleAdjunction (modulePushforward modulePullback)

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard
@[instance_reducible] local instance abelianModules (Z : RingedSpace.{u, u}) :
    Abelian (_root_.SheafOfModules.{u} (structureSheafRing Z)) :=
  _root_.SheafOfModules.instAbelian _

local instance enoughInjectivesModules (Z : RingedSpace.{u, u}) :
    EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing Z)) :=
  Stacks.Cohomology.FlatBaseChange.enoughInjectives_ringSheaf Z

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

local instance {S T : Scheme.{u}} (g : T ⟶ S) [Flat g] :
    PreservesFiniteLimits (Scheme.Modules.pullback g) := preservesFiniteLimits_pullback g

/-- The bounded-below base-change map is invertible for quasi-coherent
cohomology on a quasi-compact quasi-separated flat base-change square. -/
theorem isIso_flatSquareBaseChangePlus_of_quasicoherent {X X' S T : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
    [QuasiCompact f] [QuasiSeparated f] (h : IsPullback a b f g)
    (K : DerivedCategory.Plus X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.Plus.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    IsIso ((flatSquareBaseChangePlus h).app K) := by
  let : Flat a := MorphismProperty.of_isPullback h.flip inferInstance
  let τ := schemeBaseChange f b g a h.w
  let : NatTrans.CommShift τ ℤ := natTransCommShift_schemeBaseChange f b g a h.w
  obtain ⟨n, hn⟩ := K.property
  have hGE : K.IsGE n := (DerivedCategory.Plus.isGE_ι_obj_iff K n).mp hn
  have hτ : IsIso (τ.app K) := by
    refine DerivedCategory.Plus.isIso_app_of_isGE_of_isIso_app_single τ ?_ ?_ K n hGE ?_
    · intro L m hm
      let : L.IsGE m := hm
      let := Functor.isGE_rightDerivedFunctorPlus_obj (modulePushforward f.toLRSHom.toShHom) L m
      exact Functor.isGE_rightDerivedFunctorPlus_obj (modulePullback g.toLRSHom.toShHom) _ m
    · intro L m hm
      let : L.IsGE m := hm
      let := Functor.isGE_rightDerivedFunctorPlus_obj (modulePullback a.toLRSHom.toShHom) L m
      exact Functor.isGE_rightDerivedFunctorPlus_obj (modulePushforward b.toLRSHom.toShHom) _ m
    · intro q
      let M := (DerivedCategory.Plus.homologyFunctor X.Modules q).obj K
      let : M.IsQuasicoherent := hK q
      exact isIso_baseChangeMap_of_flat h M
  have hunit : IsIso (Scheme.Modules.pullback g).rightDerivedFunctorPlusUnith :=
    isIso_pullbackUnit g
  let : (modulePushforward f.toLRSHom.toShHom).Additive :=
    inferInstanceAs (Scheme.Modules.pushforward f).Additive
  let : (modulePushforward b.toLRSHom.toShHom).Additive :=
    inferInstanceAs (Scheme.Modules.pushforward b).Additive
  let : (modulePullback g.toLRSHom.toShHom).Additive :=
    inferInstanceAs (Scheme.Modules.pullback g).Additive
  let : (modulePullback a.toLRSHom.toShHom).Additive :=
    inferInstanceAs (Scheme.Modules.pullback a).Additive
  let : PreservesFiniteLimits (modulePullback g.toLRSHom.toShHom) :=
    preservesFiniteLimits_pullback g
  let : PreservesFiniteLimits (modulePullback a.toLRSHom.toShHom) :=
    preservesFiniteLimits_pullback a
  let F := modulePushforward f.toLRSHom.toShHom
  let F' := modulePushforward b.toLRSHom.toShHom
  let G := modulePullback g.toLRSHom.toShHom
  let G' := modulePullback a.toLRSHom.toShHom
  let hF : F.Additive := inferInstanceAs (Scheme.Modules.pushforward f).Additive
  let hF' : F'.Additive := inferInstanceAs (Scheme.Modules.pushforward b).Additive
  let hG : G.Additive := inferInstanceAs (Scheme.Modules.pullback g).Additive
  let hG' : G'.Additive := inferInstanceAs (Scheme.Modules.pullback a).Additive
  have hh := (@Stacks.Cohomology.BaseChange.isIso_derived_app_iff_isIso_derivedBaseChangePlus_app
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F F' G G' hF hF' hG hG' _ _ _ _
    (schemeModuleBaseChange f b g a h.w) K).mp hτ
  rw [moduleBaseChange_eq f b g a h.w] at hh
  exact hh

/-- Flat base change for the projective-line projection at an intrinsic perfect input. -/
theorem isIso_projectiveLineFlatBaseChangePlus {S T : Scheme.{u}} (g : T ⟶ S) [Flat g]
    (K : DerivedCategory.Plus (projectiveSpaceOver 1 S).Modules)
    (hK : RingedSpace.IsPerfect (X := (projectiveSpaceOver 1 S).toRingedSpace)
      (DerivedCategory.Plus.ι.obj K)) : IsIso ((projectiveLineFlatBaseChangePlus g).app K) :=
  isIso_flatSquareBaseChangePlus_of_quasicoherent (isPullback_projectiveSpaceOverMap 1 g) K
    (fun n ↦ PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ _ hK n)

/-- The self-base-change mate is invertible at every intrinsic perfect input. -/
theorem isIso_lineSelfBaseChangePlus (R : CommRingCat.{u})
    (K : DerivedCategory.Plus (projectiveSpaceOver 1 (Spec R)).Modules)
    (hK : RingedSpace.IsPerfect (X := (projectiveSpaceOver 1 (Spec R)).toRingedSpace)
      (DerivedCategory.Plus.ι.obj K)) : IsIso ((lineSelfBaseChangePlus R).app K) := by
  let f := projectiveSpaceOver 1 (Spec R) ↘ Spec R
  exact isIso_flatSquareBaseChangePlus_of_quasicoherent (IsPullback.of_hasPullback f f) K
    (fun n ↦ PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ _ hK n)

/-- The intrinsic perfect objects of the bounded-below derived category. -/
abbrev perfectPlus (X : Scheme.{u}) : ObjectProperty (DerivedCategory.Plus X.Modules) :=
  fun K ↦ RingedSpace.IsPerfect (X := X.toRingedSpace) (DerivedCategory.Plus.ι.obj K)

/-- The natural flat base-change isomorphism on intrinsic perfect objects. -/
@[expose] def projectiveLinePerfectFlatBaseChangePlusIso {S T : Scheme.{u}}
    (g : T ⟶ S) [Flat g] :=
  let τ := Functor.whiskerLeft (perfectPlus (projectiveSpaceOver 1 S)).ι
    (projectiveLineFlatBaseChangePlus g)
  @asIso _ _ _ _ τ ((NatTrans.isIso_iff_isIso_app τ).mpr fun K ↦ by
    change IsIso ((projectiveLineFlatBaseChangePlus g).app K.obj)
    exact isIso_projectiveLineFlatBaseChangePlus g K.obj K.property)

/-- On the intrinsic perfect subcategory the comparison is the original flat mate. -/
theorem projectiveLinePerfectFlatBaseChangePlusIso_hom_app {S T : Scheme.{u}}
    (g : T ⟶ S) [Flat g] (K : (perfectPlus (projectiveSpaceOver 1 S)).FullSubcategory) :
    (projectiveLinePerfectFlatBaseChangePlusIso g).hom.app K =
      (projectiveLineFlatBaseChangePlus g).app K.obj := rfl

/-- The natural self-base-change isomorphism on the intrinsic perfect subcategory. -/
@[expose] def lineSelfPerfectBaseChangePlusIso (R : CommRingCat.{u}) :=
  let τ := Functor.whiskerLeft (perfectPlus (projectiveSpaceOver 1 (Spec R))).ι
    (lineSelfBaseChangePlus R)
  @asIso _ _ _ _ τ ((NatTrans.isIso_iff_isIso_app τ).mpr fun K ↦ by
    change IsIso ((lineSelfBaseChangePlus R).app K.obj)
    exact isIso_lineSelfBaseChangePlus R K.obj K.property)

/-- The forward map on the perfect subcategory is the actual self-base-change mate. -/
theorem lineSelfPerfectBaseChangePlusIso_hom_app (R : CommRingCat.{u})
    (K : (perfectPlus (projectiveSpaceOver 1 (Spec R))).FullSubcategory) :
    (lineSelfPerfectBaseChangePlusIso R).hom.app K =
      (lineSelfBaseChangePlus R).app K.obj := rfl

end AlgebraicGeometry.projectiveSpaceOver

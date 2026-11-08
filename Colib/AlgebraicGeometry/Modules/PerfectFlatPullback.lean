/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOpenRestriction
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback
public import
  StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.PullbackOnRingedSpaces
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Genuine flat pullback of native perfect complexes

The actual termwise module pullback preserves local strictly perfect representatives because
flatness preserves their quasi-isomorphisms. No global strict replacement is chosen.
Implementation provenance:
`Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/FlatPullback.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, with the native Stacks perfectness predicate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]

/-- Genuine flat scheme pullback is left exact on all module sheaves. -/
@[stacks 02N4 "Exact pullback for sheaves of modules along a genuinely flat scheme morphism"]
theorem pullback_preservesFiniteLimits_of_flat : PreservesFiniteLimits (pullback f) :=
  RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat
    f.toLRSHom.toShHom (fun x => Flat.stalkMap f x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Degreewise pullback along a flat scheme morphism preserves native perfectness. -/
@[stacks 09U6 "Strict local models and exact flat pullback preserve native perfect complexes"]
theorem Complex.isPerfectComplex_flatPullback (K : CochainComplex Y.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := Y.toRingedSpace) K) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
      (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  apply RingedSpace.isPerfectComplex_of_forall_exists
  intro x
  obtain ⟨U, hx, P, hP, α, hα⟩ := hK.exists_local (f x)
  let U' : Y.Opens := U
  let V : X.Opens := f ⁻¹ᵁ U'
  let k : V.toScheme ⟶ U'.toScheme := f ∣_ U'
  let G := (pullback k).mapHomologicalComplex (ComplexShape.up ℤ)
  let eU := RingedSpace.restrictModulesIsoRestrictFunctor Y U' ≪≫
    restrictFunctorIsoPullback U'.ι
  let eV := RingedSpace.restrictModulesIsoRestrictFunctor X V ≪≫
    restrictFunctorIsoPullback V.ι
  let RY : Y.Modules ⥤ U'.toScheme.Modules := RingedSpace.restrictModules Y.toRingedSpace U'
  let RX : X.Modules ⥤ V.toScheme.Modules := RingedSpace.restrictModules X.toRingedSpace V
  have : RY.PreservesZeroMorphisms := ⟨fun _ _ => by ext _ _; rfl⟩
  have : RX.PreservesZeroMorphisms := ⟨fun _ _ => by ext _ _; rfl⟩
  let e : RY ⋙ pullback k ≅ pullback f ⋙ RX :=
    Functor.isoWhiskerRight eU (pullback k) ≪≫ pullbackComp k U'.ι ≪≫
    eqToIso (congrArg pullback (morphismRestrict_ι f U')) ≪≫
    (pullbackComp V.ι f).symm ≪≫ Functor.isoWhiskerLeft (pullback f) eV.symm
  let eK := (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app K
  have : PreservesFiniteLimits (pullback k) := pullback_preservesFiniteLimits_of_flat k
  have : QuasiIso α := hα
  have : QuasiIso (G.map α) := inferInstance
  have hs : StrictlyPerfect.IsStrictlyPerfect (G.obj P) :=
    Stacks.StrictlyPerfect.Pullback.isStrictlyPerfect_modulePullback k.toLRSHom.toShHom P hP
  exact ⟨V, hx, G.obj P, hs, G.map α ≫ eK.hom, inferInstance⟩

/-- Actual degreewise geometric pullback on the native full perfect-complex subcategories. -/
def perfectFlatPullback :
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)) ⥤
      ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  ObjectProperty.lift (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)) ⋙
      (pullback f).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => Complex.isPerfectComplex_flatPullback f K.obj K.property)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Aglib/AlgebraicGeometry/Modules/PerfectComplexes/FlatPullback.lean:88-104"
  "adaptation" "Actual flat termwise pullback preserving the native local-perfect predicate"]
  AlgebraicGeometry.Scheme.Modules.Complex.isPerfectComplex_flatPullback
  AlgebraicGeometry.Scheme.Modules.perfectFlatPullback

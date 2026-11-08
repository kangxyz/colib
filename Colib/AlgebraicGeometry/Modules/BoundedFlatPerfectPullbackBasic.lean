/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.FlatPullback

/-!
# Arbitrary pullback on bounded-above flat perfect complexes

The functor is the actual termwise geometric pullback on complexes and chain maps.
Bounded-above flat complexes are K-flat. The native K-flat pullback theorem preserves their
quasi-isomorphisms and local perfectness. Exactness uses flat quotients, never ambient
exactness of arbitrary pullback. No lower bound or flatness of the morphism is assumed.

Adapted from `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Pullback.lean`
and `BoundedFlatPullback.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The actual bounded-above flat model is K-flat for the native sheaf tensor product. -/
theorem kFlat_of_boundedAboveFlatPerfect
    {K : CochainComplex Y.Modules ℤ} (hK : boundedAboveFlatPerfectComplex Y.toRingedSpace K) :
    RingedSpace.KFlatDerivedPullback.KFlat Y.toRingedSpace K :=
  RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat
    Y.toRingedSpace K hK.2.1 hK.2.2

/-- Arbitrary termwise pullback preserves the original bounded-above flat perfect property. -/
theorem boundedAboveFlatPerfectComplex_pullback (f : X ⟶ Y)
    {K : CochainComplex Y.Modules ℤ} (hK : boundedAboveFlatPerfectComplex Y.toRingedSpace K) :
    boundedAboveFlatPerfectComplex X.toRingedSpace
      (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  obtain ⟨hp, ⟨b, hb⟩, hf⟩ := hK
  refine ⟨RingedSpace.KFlatDerivedPullback.isPerfectComplex_modulePullback
    f.toLRSHom.toShHom K
    (RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat _ K ⟨b, hb⟩ hf) hp,
    ⟨b, (CochainComplex.isStrictlyLE_iff _ b).2 ?_⟩, fun n => ?_⟩
  · intro n hn
    exact (pullback f).map_isZero (K.isZero_of_isStrictlyLE b n hn)
  · exact Stacks.SheafOfModules.modulePullback_isFlat f.toLRSHom.toShHom (K.X n) (hf n)

/-- The native K-flat theorem preserves actual quasi-isomorphisms under every pullback. -/
theorem quasiIso_pullback_of_boundedAboveFlatPerfect (f : X ⟶ Y)
    {K L : CochainComplex Y.Modules ℤ} (hK : boundedAboveFlatPerfectComplex Y.toRingedSpace K)
    (hL : boundedAboveFlatPerfectComplex Y.toRingedSpace L) (s : K ⟶ L) [QuasiIso s] :
    QuasiIso (((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) :=
  RingedSpace.KFlatDerivedPullback.quasiIso_modulePullback_of_kFlat f.toLRSHom.toShHom
    s inferInstance (kFlat_of_boundedAboveFlatPerfect hK) (kFlat_of_boundedAboveFlatPerfect hL)

end AlgebraicGeometry.Scheme.Modules

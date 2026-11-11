/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatDegree
public import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian

/-!
# The whole scalar-extension fundamental cycle

The base scheme is Noetherian and has a specified morphism to `Spec k`.
The field extension is finite, with no separability hypothesis. No reducedness
or finite-type hypothesis on the structure morphism is required. The scalar
projection is finite flat; its source is Noetherian by finiteness over the base.
Its actual rank is the full field degree, computed by pullback invariance of
`Scheme.Hom.finrank` and the rank of the finite free field algebra.

This is the native counterpart of motivic's `finitePushforward_scalar_fundamentalCycle`,
blob 37d7b9144e3024c175a3ae4e091fb579a3084ba0. The proof uses the native full-fibre
rank calculation rather than a supplied degree formula or a reduced fibre model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

local instance : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

local instance : Flat (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k E))

/-- The literal scalar projection has full field degree at every point. -/
theorem finrank_scalarProjection {X : Scheme.{u}} (q : X ⟶ Spec (.of k)) (x : X) :
    (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k E)))).finrank x =
      Module.finrank k E := by
  rw [Scheme.Hom.finrank_pullback_fst, Scheme.Hom.finrank_SpecMap_algebraMap]
  simp only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply]

/-- Actual pushforward retains all components and nilpotent lengths and multiplies
by the full scalar degree, including for inseparable field extensions. -/
theorem finitePushforward_scalar_fundamentalCycle {X : Scheme.{u}} [IsNoetherian X]
    (q : X ⟶ Spec (.of k)) :
    let p := pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    letI : IsNoetherian (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k E)))) :=
      isNoetherian_of_finiteType p
    finiteCyclePushforward p (AlgebraicCycle.fundamentalCycle _) =
      (Module.finrank k E : ℤ) • AlgebraicCycle.fundamentalCycle X := by
  dsimp only
  apply finiteCyclePushforward_fundamentalCycle_of_constant_finrank
  exact fun x => finrank_scalarProjection q x

end Stacks.Chow

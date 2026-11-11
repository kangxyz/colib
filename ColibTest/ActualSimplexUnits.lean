/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Units.UnitSheafification

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicSimplex Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite

universe u

noncomputable section

variable (R : Type u) [CommRing R] [_root_.IsReduced R]

example (n : ℕ) : Function.Bijective (Units.map (constant R n).toMonoidHom) :=
  units_constant_bijective R n

example (v : Rˣ) : constantUnitsEquiv R 0 v = Units.map (constant R 0).toMonoidHom v := rfl

example (n : ℕ) : IsIso (ringUnitsFunctor.map (structureMap R n).appTop) := inferInstance

example (k : Type u) [CommRing k] (c : k →+* R) (n : ℕ) :
    IsIso (ringUnitsFunctor.map
      (pullback.snd (structureMap k n) (Spec.map (CommRingCat.ofHom c))).appTop) :=
  inferInstance

example (k : Type u) [CommRing k] (X : Scheme.{u})
    [IsAffine X] [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (.of k)) (n : ℕ) :
    IsIso (ringUnitsFunctor.map (pullback.snd (structureMap k n) f).appTop) :=
  isIso_units_affineSchemeProjection f n

variable (k : Type u) [Field k]

example (X : SmoothSite (Spec (.of k))) [IsAffine X.left] (n : ℕ) :
    IsIso ((unitsSimplexPullback k n).hom.app (op X)) :=
  isIso_unitsSimplexPullback_affine k n X

-- No affine, normal, Noetherian, nonempty or connected caller premise.
example (n : ℕ) : IsIso (unitsSimplexPullback k n) := inferInstance

example (X : SmoothSite (Spec (.of k))) (n : ℕ) :
    IsIso ((unitsSimplexPullback k n).hom.app (op X)) := inferInstance

example (X : SmoothSite (Spec (.of k))) (n : ℕ) (v : (Γ(X.left, ⊤))ˣ) :
    (unitsSimplexPullback k n).hom.app (op X) (ULift.up (Additive.ofMul v)) =
      ULift.up (Additive.ofMul (Units.map
        (pullback.fst X.hom (structureMap k n)).appTop.hom.toMonoidHom v)) := rfl

example : HomotopyEquiv (unitSingularSheafComplex k)
    ((ChainComplex.single₀ _).obj (largeUnitsSheaf (Spec (.of k)))) :=
  unitSingularSheafHomotopyEquiv k

example : QuasiIso (unitSingularSheafHomotopyEquiv k).hom := inferInstance

example (n : ℕ) : (unitRawComplexIso k).hom.f n = 𝟙 _ := rfl

example : (sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
      (largeUnitsPresheaf (Spec (.of k))) ≅ unitSingularSheafComplex k :=
  unitSheafifiedSingularIso k

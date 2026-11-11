/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Bass.ConeGeneratorRecognition

open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval

noncomputable section
universe u
variable {S T : Arrow (Arrow LoopPrespectrum.{u})} {a b : S ⟶ T}
  (H : StrictSquare.MapHomotopy a b)

example (r : unitInterval) : H.span.at r = StrictSquare.spanMap (H.at r) := H.span_at r

example (r : unitInterval) :
    H.cone.at r = mappingConeMap (strictSquareComparisonFunctor.map (H.at r)) := H.cone_at r

example (r : unitInterval) :
    H.looped.at r = strictSquareLoopedConeFunctor.map (H.at r) := H.looped_at r

example : StrictSquare.MapHomotopy.ConeGeneratorLaw H H.cone := H.cone_generatorLaw

example : ∃! K, StrictSquare.MapHomotopy.ConeGeneratorLaw H K := by
  refine ⟨H.cone, H.cone_generatorLaw, ?_⟩
  intro K hK
  exact H.eq_cone_of_generatorLaw K hK

example (n : ℕ) (r s q : unitInterval) (x : S.left.left.space n) :
    H.cone.level n (r, StrictSquare.MapHomotopy.coneCylinder S n s
      (HomotopyPushout.cylinder S.left.hom S.hom.left n (q, x))) =
    StrictSquare.MapHomotopy.coneCylinder T n s
      (HomotopyPushout.cylinder T.left.hom T.hom.left n (q, H.source.level n (r, x))) :=
  H.cone_generatorLaw.overlap n r s q x

example (r s q : unitInterval) (x : S.left.left.space 0) :
    H.cone.level 0 (r, StrictSquare.MapHomotopy.coneCylinder S 0 s
      (HomotopyPushout.cylinder S.left.hom S.hom.left 0 (q, x))) =
    StrictSquare.MapHomotopy.coneCylinder T 0 s
      (HomotopyPushout.cylinder T.left.hom T.hom.left 0 (q, H.source.level 0 (r, x))) :=
  H.cone_generatorLaw.overlap 0 r s q x

example (n : ℕ) (r : unitInterval) (y : S.right.right.space n) :
    H.cone.level n (r, (mappingConeInclusion (StrictSquare.comparison S)).map n y) =
      (mappingConeInclusion (StrictSquare.comparison T)).map n (H.target.level n (r, y)) :=
  H.cone_generatorLaw.laurent n r y

example (n : ℕ) (r t : unitInterval)
    (γ : Path ((mappingCone (StrictSquare.comparison S)).point n)
      ((mappingCone (StrictSquare.comparison S)).point n)) :
    Path.toContinuousMap (H.looped.level n (r, γ)) t = H.cone.level n (r, γ t) :=
  H.looped_apply n r t γ

example (S : Arrow (Arrow LoopPrespectrum.{u})) :
    ∃ H : StrictSquare.MapHomotopy (𝟙 S) (𝟙 S),
      StrictSquare.MapHomotopy.ConeGeneratorLaw H H.cone := by
  let H : StrictSquare.MapHomotopy (𝟙 S) (𝟙 S) :=
    { source := Homotopy.refl _
      upper := Homotopy.refl _
      lower := Homotopy.refl _
      target := Homotopy.refl _
      commUpper := by intros; rfl
      commLower := by intros; rfl
      commRight := by intros; rfl
      commBottom := by intros; rfl }
  exact ⟨H, H.cone_generatorLaw⟩

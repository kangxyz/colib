/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.IntegralAffine

/-!
# Original zero neighborhoods from generic open restrictions

An actual zero restriction on a generic open of each integral affine smooth
scheme yields affine zero neighborhoods at every point by integral-affine
local vanishing.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Coefficient.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `3b918a1a2a6881bfa0fbf84e0bbccfeb63e1b1d3`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Each section on an integral affine model vanishes on a neighborhood of
its actual generic point. -/
def HasGenericOpenZeros (P : PresheafWithTransfers.{v} k) : Prop :=
  ∀ (T : SmoothSite (Spec (.of k))) [IsAffine T.left] [IsIntegral T.left]
    (s : sections P (Cor.mk T)), ∃ O : T.left.Opens, genericPoint T.left ∈ O ∧
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ T.hom)) (Y := T) O.ι rfl)) s = 0

/-- Generic open zeros and integral-affine local vanishing give an affine
zero neighborhood at each original point. -/
theorem exists_zero_neighborhood_of_generic_open_zeros
    (hD : IntegralAffineLocalZero k) (P : PresheafWithTransfers.{u + 1} k)
    (hP : P.IsA1Invariant) (hG : P.HasGenericOpenZeros)
    (X : SmoothSite (Spec (.of k))) (s : sections P (Cor.mk X)) (x : X.left) :
    ∃ O : X.left.Opens, IsAffineOpen O ∧ x ∈ O ∧
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) s = 0 := by
  let C := SmoothSite.integralAffineCover k X
  obtain ⟨i, t, ht⟩ := C.exists_eq x
  let T := SmoothSite.mk (C.f i ≫ X.hom)
  let f : T ⟶ X := SmoothSite.homMk (C.f i) rfl
  let : IsAffine T.left := inferInstanceAs (IsAffine (C.X i))
  let : IsIntegral T.left := inferInstanceAs (IsIntegral (C.X i))
  let : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (C.f i))
  let v := transfer P ((Cor.graphFunctor k).map f) s
  obtain ⟨V, hV, hzV⟩ := hG T v
  let A := SmoothSite.mk (V.ι ≫ T.hom)
  let a : A ⟶ T := SmoothSite.homMk V.ι rfl
  let : Nonempty A.left := ⟨⟨genericPoint T.left, hV⟩⟩
  let : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion V.ι)
  obtain ⟨O, hO, htO, hzO⟩ := hD a P hP v hzV t
  let S := SmoothSite.mk (O.ι ≫ T.hom)
  let o : S ⟶ T := SmoothSite.homMk O.ι rfl
  let g := o ≫ f
  let : IsAffine S.left := hO
  let : IsOpenImmersion g.left := inferInstanceAs (IsOpenImmersion (O.ι ≫ C.f i))
  have hg : transfer P ((Cor.graphFunctor k).map g) s = 0 := by
    rw [Functor.map_comp, transfer_comp]
    exact hzO
  exact ⟨g.left.opensRange, isAffineOpen_opensRange g.left, ⟨⟨t, htO⟩, ht⟩,
    P.zero_on_open_image_general g s hg⟩

end AlgebraicGeometry.PresheafWithTransfers

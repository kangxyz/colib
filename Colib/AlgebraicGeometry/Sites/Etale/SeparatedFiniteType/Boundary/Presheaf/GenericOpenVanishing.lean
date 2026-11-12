/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.GenericOpen
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Cokernel
public import Colib.CategoryTheory.Sites.SheafifyLocallyZero

/-!
# Generic open vanishing on the original small Nisnevich site

Affine zero neighborhoods of the original transfer presheaf give a zero
ordinary sheafification after restriction to the original small site.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Coefficient.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `3b918a1a2a6881bfa0fbf84e0bbccfeb63e1b1d3`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k]

/-- Actual zero neighborhoods generate the equalizer covering sieve on
each object of the original small site. -/
theorem zeroSieve_mem_of_generic_open_zeros
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) (hG : P.HasGenericOpenZeros)
    (X : SmoothSite (Spec (.of k))) (T : EtaleSeparatedFiniteType X.left)
    (s : ((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj P).obj (op T)) :
    Presheaf.equalizerSieve s 0 ∈ nisnevichTopology X.left T := by
  choose O hO hx hz using fun x =>
    P.exists_zero_neighborhood_of_generic_open_zeros hD hP hG ((toSmoothSite X).obj T) s x
  let : IsNoetherian T.left :=
    inferInstanceAs (IsNoetherian ((toSmoothSite X).obj T).left)
  let (x : T.left) : IsAffine (O x).toScheme := hO x
  let U (x : T.left) : EtaleSeparatedFiniteType X.left :=
    MorphismProperty.Over.mk ⊤ ((O x).ι ≫ T.hom)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let f (x : T.left) : U x ⟶ T := MorphismProperty.Over.homMk (O x).ι rfl
  let (x : T.left) : IsOpenImmersion (f x).left :=
    inferInstanceAs (IsOpenImmersion (O x).ι)
  apply Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mpr
  refine ⟨Presieve.ofArrows U f, ?_, ?_⟩
  · apply (ofArrows_mem_nisnevichPrecoverage_iff f).mpr
    exact ⟨fun _ => inferInstance, fun x => ⟨x, ⟨x, hx x⟩, rfl, inferInstance⟩⟩
  · rw [Presieve.ofArrows_le_iff]
    intro x
    let A := SmoothSite.mk ((O x).ι ≫ (T.hom ≫ X.hom))
    let a : A ⟶ (toSmoothSite X).obj T := SmoothSite.homMk (O x).ι rfl
    let e : (toSmoothSite X).obj (U x) ⟶ A :=
      SmoothSite.homMk (𝟙 _) (by simp [A, U, toSmoothSite, Category.assoc])
    have he : e ≫ a = (toSmoothSite X).map (f x) := by
      apply MorphismProperty.Over.Hom.ext
      exact Category.id_comp _
    change P.transfer ((Cor.graphFunctor k).map ((toSmoothSite X).map (f x))) s =
      P.transfer ((Cor.graphFunctor k).map ((toSmoothSite X).map (f x))) 0
    rw [map_zero, ← he, Functor.map_comp, PresheafWithTransfers.transfer_comp,
      ConcreteCategory.comp_apply]
    have hz' : P.transfer ((Cor.graphFunctor k).map a) s = 0 := hz x
    rw [hz', map_zero]

/-- The canonical ordinary sheafification of the original restricted
presheaf is zero. -/
theorem isZero_sheafify_of_generic_open_zeros
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) (hG : P.HasGenericOpenZeros)
    (X : SmoothSite (Spec (.of k))) :
    IsZero ((presheafToSheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1}).obj
      ((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj P)) :=
  Presheaf.isZero_sheafify_of_locally_zero _ _ (zeroSieve_mem_of_generic_open_zeros hD P hP hG X)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

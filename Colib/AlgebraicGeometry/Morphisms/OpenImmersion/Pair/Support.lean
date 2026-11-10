/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Basic

/-!
# Actual support and localization squares

The given support and localization squares determine original inverse-image and
union-support squares. No cartesian or flatness hypothesis is imposed.

Adapted from Quillen `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Support/Pairs.lean`
and `Support/PairSquares.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- An actual open subset, as an object of the native category of open immersions. -/
def supportOpenPair {X : Scheme.{u}} (T : X.Opens) : OpenPairs.{u} :=
  MorphismProperty.Arrow.mk T.ι inferInstance

/-- The original square given by inverse image of the support open. -/
def supportRestrictionPair {U X : Scheme.{u}} (j : U ⟶ X) (T : X.Opens) :
    supportOpenPair (j ⁻¹ᵁ T) ⟶ supportOpenPair T :=
  MorphismProperty.Arrow.homMk (j.resLE T (j ⁻¹ᵁ T) le_rfl) j (j.resLE_comp_ι le_rfl)

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)

/-- The supplied localization square, with both original scheme maps. -/
def supportedOpenRestrictionSquare :
    (MorphismProperty.Arrow.mk j' inferInstance : OpenPairs.{u}) ⟶
      MorphismProperty.Arrow.mk j inferInstance :=
  MorphismProperty.Arrow.homMk g f.right w.symm

/-- The support square gives precisely the required containment in inverse image. -/
lemma supportPair_le_preimage : S ≤ f.right ⁻¹ᵁ T := by
  intro x hx
  let y : T := f.left ⟨x, hx⟩
  have he : y.val = f.right x :=
    congrArg (fun k : S.toScheme ⟶ X => k ⟨x, hx⟩) (MorphismProperty.Arrow.w f)
  change f.right x ∈ T
  exact he ▸ y.property

omit [IsOpenImmersion j'] [IsOpenImmersion j] in
include w in
/-- The original localization map pulls back the target's support containment. -/
lemma supportedPair_target_le_preimage : j' ⁻¹ᵁ S ≤ g ⁻¹ᵁ (j ⁻¹ᵁ T) := by
  intro x hx
  have he := congrArg (fun k : U' ⟶ X => k x) w
  change f.right (j' x) = j (g x) at he
  change j (g x) ∈ T
  rw [← he]
  exact supportPair_le_preimage f hx

/-- The actual square on the supports restricted to the localization opens. -/
def supportedPairTargetSquare : supportOpenPair (j' ⁻¹ᵁ S) ⟶ supportOpenPair (j ⁻¹ᵁ T) :=
  MorphismProperty.Arrow.homMk
    (g.resLE (j ⁻¹ᵁ T) (j' ⁻¹ᵁ S) (supportedPair_target_le_preimage j' j f g w)) g
    (g.resLE_comp_ι (supportedPair_target_le_preimage j' j f g w))

include w in
/-- The same two squares pull back the union of support and localization opens. -/
lemma supportedPair_union_le_preimage :
    S ⊔ j'.opensRange ≤ f.right ⁻¹ᵁ (T ⊔ j.opensRange) := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (supportPair_le_preimage f hx)
  · rcases hx with ⟨y, rfl⟩
    right
    refine ⟨g y, ?_⟩
    exact (congrArg (fun k : U' ⟶ X => k y) w).symm

/-- The original ambient map induces the actual union-support square. -/
def supportedPairUnionSquare :
    supportOpenPair (S ⊔ j'.opensRange) ⟶ supportOpenPair (T ⊔ j.opensRange) :=
  MorphismProperty.Arrow.homMk
    (f.right.resLE (T ⊔ j.opensRange) (S ⊔ j'.opensRange)
      (supportedPair_union_le_preimage j' j f g w)) f.right
    (f.right.resLE_comp_ι (supportedPair_union_le_preimage j' j f g w))

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.SmoothSectionCommonList
public import Colib.Util.References

/-!
# A common smooth-diagonal list on the literal graph product

For `f : X ⟶ Y` and smooth `g : Y ⟶ S`, the actual graph-product pair
`X ×[S] Y ⟶ Y ×[S] Y` is a base change of the first projection of the
self-product. Native pullback symmetry and pasting identify that base change.
At every point mapping into the diagonal, one finite family generates the
actual diagonal stalk kernel and is regular both there and in the actual
graph-product stalk.

The additional hypothesis `IsLocallyNoetherian X` is explicit. This is enough
for the motivic finite-type-over-a-field application. The original source
proves the more general statement without this hypothesis by standard-smooth
and etale charts. Here native quotient-flat base change replaces that proof;
no assertion about arbitrary non-Noetherian coefficient schemes is made.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S Y X : Scheme.{u}} (g : Y ⟶ S) (f : X ⟶ Y)

/-- The native symmetry-and-pasting identification of the diagonal base-change
ambient scheme with the source-first graph ambient product. -/
def diagonalBaseChangeGraphIso :
    pullback (pullback.fst g g) f ≅ pullback (f ≫ g) g :=
  pullbackSymmetry (pullback.fst g g) f ≪≫ pullbackRightPullbackFstIso g g f

/-- The first base-change projection is the literal graph-product pair after
the native pullback isomorphism. -/
@[reassoc]
theorem diagonalBaseChangeGraphIso_inv_fst :
    (diagonalBaseChangeGraphIso g f).inv ≫ pullback.fst (pullback.fst g g) f =
      pullback.map (f ≫ g) g g g f (𝟙 Y) (𝟙 S) (by simp) (by simp) := by
  apply pullback.hom_ext <;>
    simp [diagonalBaseChangeGraphIso, Category.assoc, pullback.map]

set_option backward.isDefEq.respectTransparency.types false in
/-- A single ordered family for the actual diagonal stalk and the actual
graph-product stalk, with arbitrary parameter morphism and explicit point
transport. The source scheme is locally Noetherian; the parameter morphism
is not assumed flat. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Graph/Transversality.lean:103-143"
  "specialization" "Locally Noetherian graph source; same actual diagonal-kernel family \
    under the literal graph-product stalk map, using native quotient-flat base change"]
theorem exists_isRegular_diagonalStalkList_graphPair [Smooth g] [IsLocallyNoetherian X]
    (z : pullback (C := Scheme) (f ≫ g) g) (y : Y)
    (hz : (pullback.map (f ≫ g) g g g f (𝟙 Y) (𝟙 S) (by simp) (by simp)) z =
      pullback.diagonal g y) :
    let γ := pullback.map (f ≫ g) g g g f (𝟙 Y) (𝟙 S) (by simp) (by simp)
    ∃ (r : ℕ) (b : Fin r → (pullback g g).presheaf.stalk (γ z)),
      IsRegular ((pullback g g).presheaf.stalk (γ z)) (List.ofFn b) ∧
      Ideal.span (Set.range b) = RingHom.ker
        (((pullback g g).presheaf.stalkCongr (.of_eq hz)).hom ≫
          (pullback.diagonal g).stalkMap y).hom ∧
      IsRegular ((pullback (f ≫ g) g).presheaf.stalk z)
        (List.ofFn (fun i => (γ.stalkMap z).hom (b i))) := by
  let e := (diagonalBaseChangeGraphIso g f).symm
  have he : e.hom ≫ pullback.fst (pullback.fst g g) f =
      pullback.map (f ≫ g) g g g f (𝟙 Y) (𝟙 S) (by simp) (by simp) :=
    diagonalBaseChangeGraphIso_inv_fst g f
  dsimp only
  revert hz
  rw [← he]
  intro hz
  exact exists_isRegular_stalkList_pullbackIso_of_smooth_section
    (pullback.fst g g) (pullback.diagonal g) (pullback.diagonal_fst g) f e z y hz

end AlgebraicGeometry.Scheme.Hom

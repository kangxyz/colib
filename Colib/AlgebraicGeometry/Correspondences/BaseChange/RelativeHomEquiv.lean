/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.Pushforward
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # The relative correspondence hom-group comparison

For `r : T ⟶ S`, a `T`-scheme `X`, and a separated locally finite-type
`S)-scheme `Y`, the comparison identifies cycles on
`X ×_T (Y ×_S T)` and `X ×_S Y` by the canonical scheme isomorphism over `X`.
It supplies the hom-group bijection for the adjunction in Riou,
*Opérations de Steenrod motiviques*, arXiv:1207.3121v1, Proposition 1.4.2.
Naturality with respect to composition of relative correspondences is a
separate statement.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S T X Y : Scheme.{u}} (r : T ⟶ S) (f : X ⟶ T) (g : Y ⟶ S)

/-- The comparison of the two ambient products for the relative correspondence hom-groups. -/
def relativeCorrespondenceProductIso :
    pullback f (pullback.snd g r) ≅ pullback (f ≫ r) g :=
  pullbackSymmetry f (pullback.snd g r) ≪≫ pullbackLeftPullbackSndIso g r f ≪≫
    pullbackSymmetry g (f ≫ r)

@[reassoc (attr := simp)]
theorem relativeCorrespondenceProductIso_hom_fst :
    (relativeCorrespondenceProductIso r f g).hom ≫ pullback.fst (f ≫ r) g =
      pullback.fst f (pullback.snd g r) := by
  simp [relativeCorrespondenceProductIso, Category.assoc]

@[reassoc (attr := simp)]
theorem relativeCorrespondenceProductIso_hom_snd :
    (relativeCorrespondenceProductIso r f g).hom ≫ pullback.snd (f ≫ r) g =
      pullback.snd f (pullback.snd g r) ≫ pullback.fst g r := by
  simp [relativeCorrespondenceProductIso, Category.assoc]

private def finiteCorrespondencesPushforward {B B' X Y Y' : Scheme.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X ⟶ B'} {g' : Y' ⟶ B'}
    [IsSeparated g'] [LocallyOfFiniteType g']
    (e : pullback f g ⟶ pullback f' g') [IsFinite e]
    (he : e ≫ pullback.fst f' g' = pullback.fst f g) :
    finiteCorrespondences f g →+ finiteCorrespondences f' g' where
  toFun c := ⟨finiteCyclePushforward e c.val,
    finiteCyclePushforward_mem_finiteCorrespondences f' g' e c.val c.property.1
      (fun z hz ↦ by simpa only [Category.assoc, he] using (c.property.2 z hz).1)
      (fun z hz ↦ by simpa only [Category.assoc, he] using (c.property.2 z hz).2)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext (map_add _ c.val d.val)

variable [IsSeparated g] [LocallyOfFiniteType g]

/-- A correspondence into the base-changed target is the same signed cycle
in the canonical product over the original base. -/
def relativeCorrespondenceHomEquiv :
    finiteCorrespondences f (pullback.snd g r) ≃+ finiteCorrespondences (f ≫ r) g := by
  let e := relativeCorrespondenceProductIso r f g
  let push :=
    finiteCorrespondencesPushforward e.hom (relativeCorrespondenceProductIso_hom_fst r f g)
  let pull := finiteCorrespondencesPushforward e.inv (by
    rw [← relativeCorrespondenceProductIso_hom_fst r f g, Iso.inv_hom_id_assoc])
  exact
    { toFun := push
      invFun := pull
      left_inv := fun c ↦ Subtype.ext (by
        change finiteCyclePushforward e.inv (finiteCyclePushforward e.hom c.val) = c.val
        simp only [finiteCyclePushforward_comp_apply, e.hom_inv_id, finiteCyclePushforward_id])
      right_inv := fun c ↦ Subtype.ext (by
        change finiteCyclePushforward e.hom (finiteCyclePushforward e.inv c.val) = c.val
        simp only [finiteCyclePushforward_comp_apply, e.inv_hom_id, finiteCyclePushforward_id])
      map_add' := push.map_add }

/-- The comparison acts on the underlying cycle by the actual finite pushforward. -/
@[simp]
theorem relativeCorrespondenceHomEquiv_val (c : finiteCorrespondences f (pullback.snd g r)) :
    (relativeCorrespondenceHomEquiv r f g c).val =
      finiteCyclePushforward (relativeCorrespondenceProductIso r f g).hom c.val := by
  unfold relativeCorrespondenceHomEquiv finiteCorrespondencesPushforward
  rfl

/-- The coefficient at the transported support point is the original signed coefficient. -/
theorem relativeCorrespondenceHomEquiv_apply (c : finiteCorrespondences f (pullback.snd g r))
    (z : (pullback f (pullback.snd g r) : Scheme.{u})) :
    (relativeCorrespondenceHomEquiv r f g c).val ((relativeCorrespondenceProductIso r f g).hom z) =
      c.val z :=
  finiteCyclePushforward_apply_of_isClosedImmersion (relativeCorrespondenceProductIso r f g).hom
    c.val z

end Stacks.Chow

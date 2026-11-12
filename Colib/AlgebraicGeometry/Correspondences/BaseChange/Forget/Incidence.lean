/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.Ambient

/-!
# Actual native incidence under forgetting a separated base

The two native integral support isomorphisms give an isomorphism of their
literal fiber product over the same middle scheme. Its inclusion into the
triple product is unchanged after applying the actual forget-base map.
Nilpotents and all components of the incidence scheme are retained.

Adapted from motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/BaseChange/Forget/Incidence.lean`,
using native Stacks integral components rather than separate generators.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {S T X Y Z : Scheme.{u}} (r : T ⟶ S)
  (f : X ⟶ T) (g : Y ⟶ T) (h : Z ⟶ T) [IsSeparated r]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The actual incidence comparison uses the two support isomorphisms over the same middle. -/
def forgetBaseIncidenceMap :
    correspondenceIncidence f g h z w ⟶
      correspondenceIncidence (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) :=
  pullback.map _ _ _ _ (forgetBaseSupportIso r f g z).hom
    (forgetBaseSupportIso r g h w).hom (𝟙 Y) (by simp) (by simp)

instance : IsIso (forgetBaseIncidenceMap r f g h z w) := by
  unfold forgetBaseIncidenceMap
  infer_instance

/-- The whole incidence scheme, not a selected component, is canonically identified. -/
def forgetBaseIncidenceIso :
    correspondenceIncidence f g h z w ≅
      correspondenceIncidence (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) :=
  asIso (forgetBaseIncidenceMap r f g h z w)

@[reassoc (attr := simp)]
theorem forgetBaseIncidenceMap_fst :
    forgetBaseIncidenceMap r f g h z w ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (forgetBaseSupportIso r f g z).hom := by
  simp [forgetBaseIncidenceMap]

@[reassoc (attr := simp)]
theorem forgetBaseIncidenceMap_snd :
    forgetBaseIncidenceMap r f g h z w ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (forgetBaseSupportIso r g h w).hom := by
  simp [forgetBaseIncidenceMap]

/-- The actual incidence inclusion intertwines the actual triple-product map. -/
@[reassoc]
theorem forgetBaseIncidenceMap_inclusion :
    forgetBaseIncidenceMap r f g h z w ≫
        correspondenceIncidenceInclusion (f ≫ r) (g ≫ r) (h ≫ r)
          (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) =
      correspondenceIncidenceInclusion f g h z w ≫ forgetBaseTripleMap r f g h := by
  apply pullback.hom_ext <;> simp only [Category.assoc,
    correspondenceIncidenceInclusion_fst, correspondenceIncidenceInclusion_snd,
    correspondenceIncidenceInclusion_fst_assoc, correspondenceIncidenceInclusion_snd_assoc,
    forgetBaseIncidenceMap_fst_assoc, forgetBaseIncidenceMap_snd_assoc,
    forgetBaseSupportIso_hom_inclusion, forgetBaseTripleMap_fst, forgetBaseTripleMap_snd]

/-- The source-target map retains the original final pushforward. -/
@[reassoc]
theorem forgetBaseIncidenceMap_map :
    forgetBaseIncidenceMap r f g h z w ≫
        correspondenceIncidenceMap (f ≫ r) (g ≫ r) (h ≫ r)
          (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w) =
      correspondenceIncidenceMap f g h z w ≫ forgetBaseProductMap r f h := by
  apply pullback.hom_ext <;>
    simp [correspondenceIncidenceMap, correspondenceIncidenceLeft,
      correspondenceIncidenceRight, Category.assoc]

end Stacks.Chow

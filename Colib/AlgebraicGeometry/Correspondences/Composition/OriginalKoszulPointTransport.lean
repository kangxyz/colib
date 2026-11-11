/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalKoszulTor
public import Mathlib.Data.List.OfFn

/-!
# Original pair Koszul comparison with actual stalk point transports

SOURCE_ONLY_UNCOMPILED. This is an equality-of-points specialization of the public
original support-linear Tor comparison. The coefficient stalk may be written at
an equal support point, and the one ordered middle list may be written at an
equal Y-self-product point. Both changes use the actual structure-sheaf stalkCongr.
The coefficient action is the restriction of the existing incidence action along
the transported incidence stalk map, not a new action on another Tor model.

The middle list is transported entry by entry. Its regularity and its full
ideal-sheaf stalk equality are transported together. There is no regularity
assumption on the coefficient image, and every homological degree is allowed.
This lower interface accepts a regular middle list; the exterior application
constructs that list from its actual geometry and has no such caller premise.

Software source: Colib e7697ab8164435c7093665d02ac34f021eefb75e,
Colib/AlgebraicGeometry/Correspondences/Composition/PairOriginalKoszulTor.lean:223-256.
The input comparison uses native quotient Koszul resolutions and Tor symmetry.
This file only transports its endpoints; it does not claim a new Tor naturality
or a choice-independent comparison. See the separate report for scope and pins.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u
namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (x : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "P" => correspondenceSupportProduct f g h z w
local notation3 (prettyPrint := false) "b" => correspondenceIncidenceToSupportProduct f g h z w
local notation3 (prettyPrint := false) "a" => correspondenceIncidenceAmbientInclusion f g h z w
local notation3 (prettyPrint := false) "m" => correspondenceMiddlePair f g h

/-- Actual middle-point transport preserves both regularity and the full diagonal ideal. -/
theorem correspondenceOriginalMiddleList_stalkCongr
    (y : pullback (C := Scheme) g g) (hy : y = m (a x))
    (s : List ((pullback g g).presheaf.stalk y))
    (hs : IsRegular ((pullback g g).presheaf.stalk y) s)
    (hk : Ideal.ofList s = IdealSheafData.stalk (pullback.diagonal g).ker y) :
    let e := (pullback g g).presheaf.stalkCongr (.of_eq hy)
    let t := fun j => e.hom.hom (s.get j)
    IsRegular ((pullback g g).presheaf.stalk (m (a x))) (List.ofFn t) ∧
      IdealSheafData.stalk (pullback.diagonal g).ker (m (a x)) =
        Ideal.span (Set.range t) := by
  subst y
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    CommRingCat.hom_id, RingHom.id_apply]
  constructor
  · simpa only [List.ofFn_get] using hs
  · rw [← Ideal.ofList_ofFn, List.ofFn_get]
    exact hk.symm

/-- The original support comparison at equal actual support and middle points.
The displayed coefficient action factors through the existing incidence action. -/
def correspondenceIncidenceTorSupportLinearEquivOfPoints
    [Flat f] [Flat h] [IsSeparated g]
    (d : P) (hd : d = b x) (y : pullback (C := Scheme) g g) (hy : y = m (a x))
    (s : List ((pullback g g).presheaf.stalk y))
    (hs : IsRegular ((pullback g g).presheaf.stalk y) s)
    (hk : Ideal.ofList s = IdealSheafData.stalk (pullback.diagonal g).ker y) (n : ℕ) :
    let eC := (P).presheaf.stalkCongr (.of_eq hd)
    let eU := (pullback g g).presheaf.stalkCongr (.of_eq hy)
    let φ := correspondenceIncidenceSupportStalkMap f g h z w x
    let β := ((m).stalkMap (a x)).hom
    let := correspondenceIncidenceTorModule f g h z w x n
    let := Module.compHom (correspondenceIncidenceAmbientTor f g h z w x n)
      ((eC.hom ≫ (b).stalkMap x).hom)
    correspondenceIncidenceAmbientTor f g h z w x n ≃ₗ[(P).presheaf.stalk d]
      ((Koszul.seqComplexTensor
        (fun j => eC.inv.hom (φ (β (eU.hom.hom (s.get j)))))
        ((P).presheaf.stalk d)).homology n) := by
  subst d
  subst y
  have hC :
      (P).presheaf.stalkCongr (.of_eq (rfl : b x = b x)) =
        Iso.refl ((P).presheaf.stalk (b x)) := by
    apply Iso.ext
    exact TopCat.Presheaf.stalkSpecializes_refl (P).presheaf (b x)
  have hU :
      (pullback g g).presheaf.stalkCongr (.of_eq (rfl : m (a x) = m (a x))) =
        Iso.refl ((pullback g g).presheaf.stalk (m (a x))) := by
    apply Iso.ext
    exact TopCat.Presheaf.stalkSpecializes_refl (pullback g g).presheaf (m (a x))
  rw [hC, hU]
  dsimp only
  have ht : IsRegular ((pullback g g).presheaf.stalk (m (a x))) (List.ofFn s.get) := by
    simpa only [List.ofFn_get] using hs
  have hkt : IdealSheafData.stalk (pullback.diagonal g).ker (m (a x)) =
      Ideal.span (Set.range s.get) := by
    rw [← Ideal.ofList_ofFn, List.ofFn_get]
    exact hk.symm
  simpa only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, CommRingCat.hom_id,
    RingHom.id_apply, correspondenceIncidenceTorSupportModule] using
      correspondenceIncidenceTorOriginalSupportLinearEquiv f g h z w x s.get ht hkt n

end Stacks.Chow

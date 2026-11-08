/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.OpenSectionPulledStalk
public import Colib.AlgebraicGeometry.Correspondences.Composition.PulledStalkModules
public import Colib.AlgebraicGeometry.Correspondences.Graph.NormalIncidence

/-!
# Actual pulled-support Tor for left identity components

The target projection of an actual diagonal component of a normal locally
Noetherian scheme is open. Its actual inverse image in the triple product is
therefore an open section of the projection to the right adjacent product.
The native ideal-comap stalk comparison identifies the other actual pulled
support with scalar extension. Native Tor symmetry restores the original
left/right order after this calculation.

Degree zero is the actual incidence stalk with its full triple-product action.
Positive Tor vanishes when the outer source is flat, hence over every field.
At an actual generic incidence point, degree-zero length is one because the
incidence is open in the original right integral support and is reduced.
No integral, connected or nonempty ambient scheme is assumed. In particular,
this does not assert transversality for arbitrary left graph components.

Implementation source: `motivic_source_a6805c4`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Tor.lean`,
`isZero_incidenceTor_succ_componentIdentity_left`,
`incidenceTorCoefficient_componentIdentity_left` and its coefficient-one theorem.
The finite-component assembly in `Identity/Units.lean` is not claimed here.
Native references: Stacks Tags 01PB, 0357 and 00M3; EGA III, 6.3.5 (i), for Tor symmetry.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The actual left inverse-image support gives a cartesian square over the middle factor. -/
theorem isPullback_correspondenceLeftPulledProjection (z : pullback (C := Scheme) f g) :
    IsPullback (correspondenceLeftPulledProjection f g h z)
      (correspondenceLeftPulledInclusion f g h z ≫
        pullback.snd (pullback.snd f g) (pullback.fst g h))
      ((integralComponentAt z).subschemeι ≫ pullback.snd f g) (pullback.fst g h) :=
  (isPullback_correspondenceLeftPulled f g h z).flip.paste_vert
    (IsPullback.of_hasPullback (pullback.snd f g) (pullback.fst g h))

/-- An open target projection remains open on the actual left pulled support. -/
theorem isOpenImmersion_leftPulled_snd
    (z : pullback (C := Scheme) f g)
    [IsOpenImmersion ((integralComponentAt z).subschemeι ≫ pullback.snd f g)] :
    IsOpenImmersion (correspondenceLeftPulledInclusion f g h z ≫
      pullback.snd (pullback.snd f g) (pullback.fst g h)) :=
  MorphismProperty.of_isPullback
    (isPullback_correspondenceLeftPulledProjection f g h z) inferInstance

variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The map to the left pulled support preserves the original first incidence projection. -/
@[reassoc (attr := simp)]
theorem correspondenceIncidenceToLeftPulled_projection :
    correspondenceIncidenceToLeftPulled f g h z w ≫
      correspondenceLeftPulledProjection f g h z = pullback.fst _ _ := by
  simp only [correspondenceIncidenceToLeftPulled, correspondenceLeftPulledProjection,
    Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]

/-- The actual incidence is the scheme-theoretic inverse image of the right support
inside the left pulled support. -/
theorem isPullback_correspondenceIncidenceToLeftPulled :
    IsPullback (correspondenceIncidenceToLeftPulled f g h z w) (pullback.snd _ _)
      (correspondenceLeftPulledInclusion f g h z ≫
        pullback.snd (pullback.snd f g) (pullback.fst g h))
      (integralComponentAt w).subschemeι := by
  have H : IsPullback
      (correspondenceIncidenceToLeftPulled f g h z w ≫
        correspondenceLeftPulledProjection f g h z) (pullback.snd _ _)
      ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt w).subschemeι ≫ pullback.fst g h) := by
    rw [correspondenceIncidenceToLeftPulled_projection]
    exact IsPullback.of_hasPullback
      ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt w).subschemeι ≫ pullback.fst g h)
  exact H.of_right (by simp only [← Category.assoc,
    correspondenceIncidenceToLeftPulled_inclusion, correspondenceIncidenceInclusion_snd])
    (isPullback_correspondenceLeftPulledProjection f g h z)

/-- The original incidence scheme is the native comap subscheme inside the left support. -/
def correspondenceIncidenceLeftRestrictionIso :
    correspondenceIncidence f g h z w ≅
      ((integralComponentAt w).comap
        (correspondenceLeftPulledInclusion f g h z ≫
          pullback.snd (pullback.snd f g) (pullback.fst g h))).subscheme :=
  (isPullback_correspondenceIncidenceToLeftPulled f g h z w).isoPullback ≪≫
    ((integralComponentAt w).comapIso
      (correspondenceLeftPulledInclusion f g h z ≫
        pullback.snd (pullback.snd f g) (pullback.fst g h))).symm

/-- The comap identification retains the actual inclusion into the left pulled support. -/
@[reassoc (attr := simp)]
theorem correspondenceIncidenceLeftRestrictionIso_hom_subschemeι :
    (correspondenceIncidenceLeftRestrictionIso f g h z w).hom ≫
      ((integralComponentAt w).comap
        (correspondenceLeftPulledInclusion f g h z ≫
          pullback.snd (pullback.snd f g) (pullback.fst g h))).subschemeι =
        correspondenceIncidenceToLeftPulled f g h z w := by
  simp only [correspondenceIncidenceLeftRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Scheme.IdealSheafData.comapIso_inv_subschemeι,
    IsPullback.isoPullback_hom_fst]

/-- The actual incidence/comap point lies over the original left pulled-support point. -/
theorem correspondenceIncidence_leftRestriction_point_eq
    (t : correspondenceIncidence f g h z w) :
    correspondenceIncidenceToLeftPulled f g h z w t =
      ((integralComponentAt w).comap
        (correspondenceLeftPulledInclusion f g h z ≫
          pullback.snd (pullback.snd f g) (pullback.fst g h))).subschemeι
        ((correspondenceIncidenceLeftRestrictionIso f g h z w).hom t) :=
  (congrArg (fun m => m t)
    (correspondenceIncidenceLeftRestrictionIso_hom_subschemeι f g h z w)).symm

section OpenLeft

variable [IsOpenImmersion ((integralComponentAt z).subschemeι ≫ pullback.snd f g)]

/-- Actual positive pulled-support Tor vanishes when the left target projection is open
and the outer source is flat. The Tor arguments retain their original left/right order. -/
theorem isZero_correspondencePulledStalkTor_succ_of_open_left [Flat f]
    (t : correspondenceIncidence f g h z w) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t))) (n + 1)).obj
      (correspondenceIncidenceLeftPulledStalkModule f g h z w t)).obj
      (correspondenceIncidenceRightPulledStalkModule f g h z w t)) := by
  have := isOpenImmersion_leftPulled_snd f g h z
  have hz := Scheme.Hom.isZero_comapStalkTor_succ_of_eq
    (correspondenceLeftPulledInclusion f g h z)
    (pullback.snd (pullback.snd f g) (pullback.fst g h)) (integralComponentAt w)
    (correspondenceIncidenceToLeftPulled f g h z w t)
    (correspondenceIncidenceInclusion f g h z w t)
    (correspondenceIncidenceToRightPulled f g h z w t)
    ((correspondenceIncidenceLeftRestrictionIso f g h z w).hom t)
    (correspondenceIncidence_leftPulled_point_eq f g h z w t)
    (correspondenceIncidence_rightPulled_point_eq f g h z w t)
    (correspondenceIncidence_leftRestriction_point_eq f g h z w t) n
  let A := (correspondenceTripleProduct f g h).presheaf.stalk
    (correspondenceIncidenceInclusion f g h z w t)
  let L := correspondenceIncidenceLeftPulledStalkModule f g h z w t
  let R := correspondenceIncidenceRightPulledStalkModule f g h z w t
  exact IsZero.of_iso hz
    (((Tor_iso_Tor' A (n + 1)).app L).app R ≪≫
      (((torFlip_iso_Tor' A (n + 1)).app L).app R).symm)

/-- Degree zero is the actual incidence stalk with its literal triple-product action. -/
def correspondencePulledStalkTorZeroIso_of_open_left
    (t : correspondenceIncidence f g h z w) :
    (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t))) 0).obj
      (correspondenceIncidenceLeftPulledStalkModule f g h z w t)).obj
      (correspondenceIncidenceRightPulledStalkModule f g h z w t)) ≅
    (ModuleCat.restrictScalars
      ((correspondenceIncidenceInclusion f g h z w).stalkMap t).hom).obj
      (ModuleCat.of ((correspondenceIncidence f g h z w).presheaf.stalk t)
        ((correspondenceIncidence f g h z w).presheaf.stalk t)) := by
  have := isOpenImmersion_leftPulled_snd f g h z
  let i := correspondenceLeftPulledInclusion f g h z
  let p := pullback.snd (pullback.snd f g) (pullback.fst g h)
  let j := correspondenceIncidenceToLeftPulled f g h z w
  let I := integralComponentAt w
  let e := correspondenceIncidenceLeftRestrictionIso f g h z w
  let c := j t
  let x := correspondenceIncidenceInclusion f g h z w t
  let hc := correspondenceIncidence_leftPulled_point_eq f g h z w t
  let hj := correspondenceIncidence_leftRestriction_point_eq f g h z w t
  let q := (((correspondenceTripleProduct f g h).presheaf.stalkCongr
    (.of_eq hc)).hom ≫ i.stalkMap c).hom
  let a := (j.stalkMap t).hom
  let d := (((correspondenceLeftPulledIdeal f g h z).subscheme.presheaf.stalkCongr
    (.of_eq hj)).hom ≫ (I.comap (i ≫ p)).subschemeι.stalkMap (e.hom t)).hom
  let b := (e.hom.stalkMap t).hom
  let eb := (asIso (e.hom.stalkMap t)).commRingCatIsoToRingEquiv
  have he : e.hom ≫ (I.comap (i ≫ p)).subschemeι = j :=
    correspondenceIncidenceLeftRestrictionIso_hom_subschemeι f g h z w
  have hdb : b.comp d = a := by
    change ((((correspondenceLeftPulledIdeal f g h z).subscheme.presheaf.stalkCongr
      (.of_eq hj)).hom ≫ (I.comap (i ≫ p)).subschemeι.stalkMap (e.hom t)) ≫
        e.hom.stalkMap t).hom = (j.stalkMap t).hom
    apply congrArg CommRingCat.Hom.hom
    simpa only [Scheme.Hom.stalkMap_comp, Category.assoc] using
      (Scheme.Hom.stalkMap_congr_hom j
        (e.hom ≫ (I.comap (i ≫ p)).subschemeι) he.symm t).symm
  let eqv' :
      (ModuleCat.restrictScalars d).obj
        (ModuleCat.of ((I.comap (i ≫ p)).subscheme.presheaf.stalk (e.hom t))
          ((I.comap (i ≫ p)).subscheme.presheaf.stalk (e.hom t))) ≅
      (ModuleCat.restrictScalars a).obj
        (ModuleCat.of ((correspondenceIncidence f g h z w).presheaf.stalk t)
          ((correspondenceIncidence f g h z w).presheaf.stalk t)) :=
    (ModuleCat.restrictScalars d).mapIso (ModuleCat.restrictScalarsIsoOfEquiv eb).symm ≪≫
      (ModuleCat.restrictScalarsComp'App d b a hdb.symm _).symm
  have hqa : a.comp q = ((correspondenceIncidenceInclusion f g h z w).stalkMap t).hom := by
    change ((((correspondenceTripleProduct f g h).presheaf.stalkCongr
      (.of_eq hc)).hom ≫ i.stalkMap c) ≫ j.stalkMap t).hom = _
    apply congrArg CommRingCat.Hom.hom
    simpa only [Scheme.Hom.stalkMap_comp, Category.assoc] using
      (Scheme.Hom.stalkMap_congr_hom (correspondenceIncidenceInclusion f g h z w)
        (j ≫ i) (by simp [j, i]) t).symm
  let A := (correspondenceTripleProduct f g h).presheaf.stalk x
  let L := correspondenceIncidenceLeftPulledStalkModule f g h z w t
  let R := correspondenceIncidenceRightPulledStalkModule f g h z w t
  exact (((Tor_iso_Tor' A 0).app L).app R ≪≫
      (((torFlip_iso_Tor' A 0).app L).app R).symm) ≪≫
    Scheme.Hom.comapStalkTorZeroIsoOfEq i p I c x
      (correspondenceIncidenceToRightPulled f g h z w t) (e.hom t) hc
      (correspondenceIncidence_rightPulled_point_eq f g h z w t) hj ≪≫
    (ModuleCat.restrictScalars q).mapIso eqv' ≪≫
    (ModuleCat.restrictScalarsComp'App q a
      ((correspondenceIncidenceInclusion f g h z w).stalkMap t).hom hqa.symm _).symm

end OpenLeft

end Stacks.Chow

namespace Stacks.Chow

/-- The two projections agree on the actual diagonal component, so the target projection
is open on a normal locally Noetherian source. This assertion is specific to the identity. -/
theorem isOpenImmersion_integralComponentAt_diagonal_snd
    {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [IsLocallyNoetherian X] [IsNormal X] (s : genericPoints X) :
    IsOpenImmersion
      ((integralComponentAt (correspondenceGraphMap f f (𝟙 X) (by simp) s.val)).subschemeι ≫
        pullback.snd f f) := by
  have hdiag := integralComponentAt_graphMap_snd f f (𝟙 X) (by simp) s.val
  simp only [Category.comp_id] at hdiag
  rw [hdiag]
  exact isOpenImmersion_integralComponentAt_graphMap_fst f f (𝟙 X) (by simp) s

section Identity

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f]
  [IsLocallyNoetherian X] [IsNormal X]
  (z : pullback (C := Scheme) f g) (s : genericPoints X)

local notation "δ" => correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val

/-- Every actual left identity-component incidence has zero positive pulled-support Tor.
The outer source's flatness is enough; the finite support is not assumed flat. -/
theorem isZero_correspondencePulledStalkTor_succ_diagonal_left [Flat f]
    (t : correspondenceIncidence f f g δ z) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((correspondenceTripleProduct f f g).presheaf.stalk
      (correspondenceIncidenceInclusion f f g δ z t))) (n + 1)).obj
      (correspondenceIncidenceLeftPulledStalkModule f f g δ z t)).obj
      (correspondenceIncidenceRightPulledStalkModule f f g δ z t)) := by
  have := isOpenImmersion_integralComponentAt_diagonal_snd f s
  exact isZero_correspondencePulledStalkTor_succ_of_open_left f f g δ z t n

/-- Left identity degree zero is the original incidence stalk with its actual ambient action.
This isomorphism requires no flatness assumption. -/
def correspondencePulledStalkTorZeroIso_diagonal_left
    (t : correspondenceIncidence f f g δ z) :
    (((Tor (ModuleCat ((correspondenceTripleProduct f f g).presheaf.stalk
      (correspondenceIncidenceInclusion f f g δ z t))) 0).obj
      (correspondenceIncidenceLeftPulledStalkModule f f g δ z t)).obj
      (correspondenceIncidenceRightPulledStalkModule f f g δ z t)) ≅
    (ModuleCat.restrictScalars
      ((correspondenceIncidenceInclusion f f g δ z).stalkMap t).hom).obj
      (ModuleCat.of ((correspondenceIncidence f f g δ z).presheaf.stalk t)
        ((correspondenceIncidence f f g δ z).presheaf.stalk t)) := by
  have := isOpenImmersion_integralComponentAt_diagonal_snd f s
  exact correspondencePulledStalkTorZeroIso_of_open_left f f g δ z t

/-- Left identity degree-zero length is the full actual incidence local-ring length. -/
theorem length_correspondencePulledStalkTor_zero_diagonal_left
    (t : correspondenceIncidence f f g δ z) :
    Module.length ((correspondenceTripleProduct f f g).presheaf.stalk
      (correspondenceIncidenceInclusion f f g δ z t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f f g).presheaf.stalk
        (correspondenceIncidenceInclusion f f g δ z t))) 0).obj
        (correspondenceIncidenceLeftPulledStalkModule f f g δ z t)).obj
        (correspondenceIncidenceRightPulledStalkModule f f g δ z t)) =
    Module.length ((correspondenceIncidence f f g δ z).presheaf.stalk t)
      ((correspondenceIncidence f f g δ z).presheaf.stalk t) := by
  rw [(correspondencePulledStalkTorZeroIso_diagonal_left f g z s t).toLinearEquiv.length_eq]
  let inc := correspondenceIncidenceInclusion f f g δ z
  let q := (inc.stalkMap t).hom
  let A := (correspondenceIncidence f f g δ z).presheaf.stalk t
  let M := ModuleCat.of A A
  let := q.toAlgebra
  let : IsScalarTower ((correspondenceTripleProduct f f g).presheaf.stalk (inc t)) A
      ((ModuleCat.restrictScalars q).obj M) := ⟨fun r a m => by
    change (q r * a) • m = q r • (a • m)
    exact mul_smul (q r) a m⟩
  exact Module.length_eq_of_surjective (R := A)
    (M := (ModuleCat.restrictScalars q).obj M) (inc.stalkMap_surjective t)

/-- At a generic point of the actual left identity incidence, degree-zero length is one.
Reducedness is proved by its open projection to the original right integral support. -/
theorem length_correspondencePulledStalkTor_zero_diagonal_left_eq_one
    (t : correspondenceIncidence f f g δ z) (ht : IsMax t) :
    Module.length ((correspondenceTripleProduct f f g).presheaf.stalk
      (correspondenceIncidenceInclusion f f g δ z t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f f g).presheaf.stalk
        (correspondenceIncidenceInclusion f f g δ z t))) 0).obj
        (correspondenceIncidenceLeftPulledStalkModule f f g δ z t)).obj
        (correspondenceIncidenceRightPulledStalkModule f f g δ z t)) = 1 := by
  rw [length_correspondencePulledStalkTor_zero_diagonal_left f g z s t]
  have := isOpenImmersion_correspondenceIncidence_snd_diagonal f g s z
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  have : IsReduced (correspondenceIncidence f f g δ z) :=
    isReduced_of_isOpenImmersion (pullback.snd
      ((integralComponentAt δ).subschemeι ≫ pullback.snd f f)
      ((integralComponentAt z).subschemeι ≫ pullback.fst f g))
  exact length_stalk_eq_one_of_isMax ht

end Identity

end Stacks.Chow

namespace Stacks.Chow

section IdentityOverField

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [IsSeparated f]
  [IsLocallyNoetherian X] [IsNormal X]
  (z : pullback (C := Scheme) f g) (s : genericPoints X)

/-- Left identity components over an arbitrary field have zero positive actual pulled Tor.
Flatness of the outer source is inferred, not provided as a support-flatness assumption. -/
theorem isZero_correspondencePulledStalkTor_succ_identity_left
    (t : correspondenceIncidence f f g
      (correspondenceGraphMap f f (𝟙 X) (by simp) s.val) z) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((correspondenceTripleProduct f f g).presheaf.stalk
      (correspondenceIncidenceInclusion f f g
        (correspondenceGraphMap f f (𝟙 X) (by simp) s.val) z t))) (n + 1)).obj
      (correspondenceIncidenceLeftPulledStalkModule f f g
        (correspondenceGraphMap f f (𝟙 X) (by simp) s.val) z t)).obj
      (correspondenceIncidenceRightPulledStalkModule f f g
        (correspondenceGraphMap f f (𝟙 X) (by simp) s.val) z t)) :=
  isZero_correspondencePulledStalkTor_succ_diagonal_left f g z s t n

end IdentityOverField

end Stacks.Chow

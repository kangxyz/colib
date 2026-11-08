/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.OpenSectionPulledStalk
public import Colib.AlgebraicGeometry.Intersection.OpenStalkComparison
public import Colib.AlgebraicGeometry.Correspondences.Composition.PulledStalkModules
public import Colib.AlgebraicGeometry.Correspondences.Graph.NormalIncidence

/-!
# Actual pulled-support Tor for graph and identity incidences

The actual right pulled subscheme projects openly to the left adjacent product
when the right support is a graph component over a normal locally Noetherian
source. This is a cartesian base change, not a flatness assertion about a finite
support. The actual incidence is the inverse-image closed subscheme inside that
open section, with the original inclusion and projection maps.

At every actual incidence point, native Tor of the two literal pulled-support
stalk modules has degree zero equal to the actual incidence stalk, and all
positive degrees vanish when the outer target is flat over the base. For an
identity over an arbitrary field that flatness is automatic. No global integral,
connected or nonempty ambient scheme is assumed. The comparison with the other
ambient Tor realization and the finite-cycle unit assembly are separate results.

Implementation source: `motivic_source_a6805c4`,
`Composition/Identity/Tor.lean`,
`isZero_incidenceTor_succ_componentIdentity_right` and
`incidenceTorCoefficient_componentIdentity_right`; and the cartesian geometry in
`Composition/Incidence/GlobalAmbientTorComparison.lean`.
References: Stacks, Tags 01PB, 0098 and 0357. These are local pulled-support Tor
statements, not yet the Euler coefficient or a Cor category unit law.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The right pulled support and its original support form the actual cartesian square
above the middle factor. The left vertical map is the composite open-section candidate. -/
theorem isPullback_correspondenceRightPulledProjection (w : pullback (C := Scheme) g h) :
    IsPullback (correspondenceRightPulledProjection f g h w)
      (correspondenceRightPulledInclusion f g h w ≫
        pullback.fst (pullback.snd f g) (pullback.fst g h))
      ((integralComponentAt w).subschemeι ≫ pullback.fst g h) (pullback.snd f g) := by
  have H : IsPullback (correspondenceRightPulledInclusion f g h w)
      (correspondenceRightPulledProjection f g h w)
      (pullback.snd (pullback.snd f g) (pullback.fst g h))
      (integralComponentAt w).subschemeι := by
    refine IsPullback.of_iso_pullback ⟨?_⟩
      ((integralComponentAt w).comapIso
        (pullback.snd (pullback.snd f g) (pullback.fst g h))) ?_ rfl
    · simp only [correspondenceRightPulledProjection, Category.assoc,
        ← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
    · exact Scheme.IdealSheafData.comapIso_hom_fst _ _
  exact H.flip.paste_vert
    (IsPullback.of_hasPullback (pullback.snd f g) (pullback.fst g h)).flip

/-- A literal open source projection remains open on the actual right pulled subscheme. -/
theorem isOpenImmersion_rightPulled_fst
    (w : pullback (C := Scheme) g h)
    [IsOpenImmersion ((integralComponentAt w).subschemeι ≫ pullback.fst g h)] :
    IsOpenImmersion (correspondenceRightPulledInclusion f g h w ≫
      pullback.fst (pullback.snd f g) (pullback.fst g h)) :=
  MorphismProperty.of_isPullback
    (isPullback_correspondenceRightPulledProjection f g h w) inferInstance

variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The map to the right pulled subscheme retains the original incidence projection. -/
@[reassoc (attr := simp)]
theorem correspondenceIncidenceToRightPulled_projection :
    correspondenceIncidenceToRightPulled f g h z w ≫
      correspondenceRightPulledProjection f g h w = pullback.snd _ _ := by
  simp [correspondenceIncidenceToRightPulled, correspondenceRightPulledProjection]

/-- The incidence is the actual inverse image of the left support inside the right
pulled support. This preserves the scheme structure, not only the support set. -/
theorem isPullback_correspondenceIncidenceToRightPulled :
    IsPullback (correspondenceIncidenceToRightPulled f g h z w) (pullback.fst _ _)
      (correspondenceRightPulledInclusion f g h w ≫
        pullback.fst (pullback.snd f g) (pullback.fst g h))
      (integralComponentAt z).subschemeι := by
  have H : IsPullback
      (correspondenceIncidenceToRightPulled f g h z w ≫
        correspondenceRightPulledProjection f g h w) (pullback.fst _ _)
      ((integralComponentAt w).subschemeι ≫ pullback.fst g h)
      ((integralComponentAt z).subschemeι ≫ pullback.snd f g) := by
    rw [correspondenceIncidenceToRightPulled_projection]
    exact (IsPullback.of_hasPullback
      ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt w).subschemeι ≫ pullback.fst g h)).flip
  exact H.of_right (by simp only [← Category.assoc,
    correspondenceIncidenceToRightPulled_inclusion, correspondenceIncidenceInclusion_fst])
    (isPullback_correspondenceRightPulledProjection f g h w)

/-- The actual incidence is the native comap subscheme inside the right pulled support. -/
def correspondenceIncidenceRightRestrictionIso :
    correspondenceIncidence f g h z w ≅
      ((integralComponentAt z).comap
        (correspondenceRightPulledInclusion f g h w ≫
          pullback.fst (pullback.snd f g) (pullback.fst g h))).subscheme :=
  (isPullback_correspondenceIncidenceToRightPulled f g h z w).isoPullback ≪≫
    ((integralComponentAt z).comapIso
      (correspondenceRightPulledInclusion f g h w ≫
        pullback.fst (pullback.snd f g) (pullback.fst g h))).symm

/-- The incidence/comap isomorphism preserves the actual map into the right support. -/
@[reassoc (attr := simp)]
theorem correspondenceIncidenceRightRestrictionIso_hom_subschemeι :
    (correspondenceIncidenceRightRestrictionIso f g h z w).hom ≫
      ((integralComponentAt z).comap
        (correspondenceRightPulledInclusion f g h w ≫
          pullback.fst (pullback.snd f g) (pullback.fst g h))).subschemeι =
        correspondenceIncidenceToRightPulled f g h z w := by
  simp [correspondenceIncidenceRightRestrictionIso]

/-- The actual incidence point maps to the specified point of the right pulled support. -/
theorem correspondenceIncidence_rightRestriction_point_eq
    (t : correspondenceIncidence f g h z w) :
    correspondenceIncidenceToRightPulled f g h z w t =
      ((integralComponentAt z).comap
        (correspondenceRightPulledInclusion f g h w ≫
          pullback.fst (pullback.snd f g) (pullback.fst g h))).subschemeι
        ((correspondenceIncidenceRightRestrictionIso f g h z w).hom t) :=
  (congrArg (fun m => m t)
    (correspondenceIncidenceRightRestrictionIso_hom_subschemeι f g h z w)).symm

section OpenRight

variable [IsOpenImmersion ((integralComponentAt w).subschemeι ≫ pullback.fst g h)]

/-- Actual positive pulled-support Tor vanishes at every incidence point when the
right support projects openly and the outer target is flat. -/
theorem isZero_correspondencePulledStalkTor_succ_of_open_right [Flat h]
    (t : correspondenceIncidence f g h z w) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t))) (n + 1)).obj
      (correspondenceIncidenceLeftPulledStalkModule f g h z w t)).obj
      (correspondenceIncidenceRightPulledStalkModule f g h z w t)) := by
  have := isOpenImmersion_rightPulled_fst f g h w
  exact Scheme.Hom.isZero_comapStalkTor_succ_of_eq
    (correspondenceRightPulledInclusion f g h w)
    (pullback.fst (pullback.snd f g) (pullback.fst g h)) (integralComponentAt z)
    (correspondenceIncidenceToRightPulled f g h z w t)
    (correspondenceIncidenceInclusion f g h z w t)
    (correspondenceIncidenceToLeftPulled f g h z w t)
    ((correspondenceIncidenceRightRestrictionIso f g h z w).hom t)
    (correspondenceIncidence_rightPulled_point_eq f g h z w t)
    (correspondenceIncidence_leftPulled_point_eq f g h z w t)
    (correspondenceIncidence_rightRestriction_point_eq f g h z w t) n

/-- Degree zero is the actual incidence stalk with its literal triple-product action. -/
def correspondencePulledStalkTorZeroIso_of_open_right
    (t : correspondenceIncidence f g h z w) :
    (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t))) 0).obj
      (correspondenceIncidenceLeftPulledStalkModule f g h z w t)).obj
      (correspondenceIncidenceRightPulledStalkModule f g h z w t)) ≅
    (ModuleCat.restrictScalars
      ((correspondenceIncidenceInclusion f g h z w).stalkMap t).hom).obj
      (ModuleCat.of ((correspondenceIncidence f g h z w).presheaf.stalk t)
        ((correspondenceIncidence f g h z w).presheaf.stalk t)) := by
  have := isOpenImmersion_rightPulled_fst f g h w
  let i := correspondenceRightPulledInclusion f g h w
  let p := pullback.fst (pullback.snd f g) (pullback.fst g h)
  let j := correspondenceIncidenceToRightPulled f g h z w
  let I := integralComponentAt z
  let e := correspondenceIncidenceRightRestrictionIso f g h z w
  let c := j t
  let x := correspondenceIncidenceInclusion f g h z w t
  let hc := correspondenceIncidence_rightPulled_point_eq f g h z w t
  let hj := correspondenceIncidence_rightRestriction_point_eq f g h z w t
  let q := (((correspondenceTripleProduct f g h).presheaf.stalkCongr
    (.of_eq hc)).hom ≫ i.stalkMap c).hom
  let a := (j.stalkMap t).hom
  let eqv := Scheme.stalkModuleIsoOfOpenSquare (I.comap (i ≫ p)).subschemeι j e.hom
    (𝟙 _) (by simpa [e, j, i, p, I] using
      correspondenceIncidenceRightRestrictionIso_hom_subschemeι f g h z w)
    c (e.hom t) c t hj rfl rfl rfl
  let eqv' :
      (ModuleCat.restrictScalars
        (((correspondenceRightPulledIdeal f g h w).subscheme.presheaf.stalkCongr
          (.of_eq hj)).hom ≫ (I.comap (i ≫ p)).subschemeι.stalkMap (e.hom t)).hom).obj
        (ModuleCat.of ((I.comap (i ≫ p)).subscheme.presheaf.stalk (e.hom t))
          ((I.comap (i ≫ p)).subscheme.presheaf.stalk (e.hom t))) ≅
      (ModuleCat.restrictScalars a).obj
        (ModuleCat.of ((correspondenceIncidence f g h z w).presheaf.stalk t)
          ((correspondenceIncidence f g h z w).presheaf.stalk t)) := by
    simpa only [Scheme.Hom.stalkMap_id, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] using eqv
  have hqa : a.comp q = ((correspondenceIncidenceInclusion f g h z w).stalkMap t).hom := by
    change ((((correspondenceTripleProduct f g h).presheaf.stalkCongr
      (.of_eq hc)).hom ≫ i.stalkMap c) ≫ j.stalkMap t).hom = _
    simpa only [Scheme.Hom.stalkMap_id, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, Category.comp_id,
      Category.assoc] using congrArg CommRingCat.Hom.hom
        (Scheme.Hom.stalkMap_square_of_eq j i (𝟙 _)
          (correspondenceIncidenceInclusion f g h z w)
          (by simp [j, i]) t c t x rfl rfl hc rfl)
  exact Scheme.Hom.comapStalkTorZeroIsoOfEq i p I c x
      (correspondenceIncidenceToLeftPulled f g h z w t) (e.hom t) hc
      (correspondenceIncidence_leftPulled_point_eq f g h z w t) hj ≪≫
    (ModuleCat.restrictScalars q).mapIso eqv' ≪≫
    (ModuleCat.restrictScalarsComp'App q a
      ((correspondenceIncidenceInclusion f g h z w).stalkMap t).hom hqa.symm _).symm

end OpenRight

section Graph

variable (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g) [IsSeparated h]
  [IsLocallyNoetherian Y] [IsNormal Y] (s : genericPoints Y)

/-- Genuine graph-component incidence has zero positive Tor of its two actual pulled stalks. -/
theorem isZero_correspondencePulledStalkTor_succ_graph_right [Flat h]
    (t : correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t))) (n + 1)).obj
      (correspondenceIncidenceLeftPulledStalkModule f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t)).obj
      (correspondenceIncidenceRightPulledStalkModule f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t)) := by
  have := isOpenImmersion_integralComponentAt_graphMap_fst g h ψ hψ s
  exact isZero_correspondencePulledStalkTor_succ_of_open_right f g h z _ t n

/-- Genuine graph-component degree zero is the actual incidence stalk, without flatness. -/
def correspondencePulledStalkTorZeroIso_graph_right
    (t : correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)) :
    (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t))) 0).obj
      (correspondenceIncidenceLeftPulledStalkModule f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t)).obj
      (correspondenceIncidenceRightPulledStalkModule f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t)) ≅
    (ModuleCat.restrictScalars
      ((correspondenceIncidenceInclusion f g h z
        (correspondenceGraphMap g h ψ hψ s.val)).stalkMap t).hom).obj
      (ModuleCat.of
        ((correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)).presheaf.stalk t)
        ((correspondenceIncidence f g h z
          (correspondenceGraphMap g h ψ hψ s.val)).presheaf.stalk t)) := by
  have := isOpenImmersion_integralComponentAt_graphMap_fst g h ψ hψ s
  exact correspondencePulledStalkTorZeroIso_of_open_right f g h z _ t

/-- Degree-zero length is the full actual incidence local-ring length, including infinity. -/
theorem length_correspondencePulledStalkTor_zero_graph_right
    (t : correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)) :
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
        (correspondenceIncidenceInclusion f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t))) 0).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t)).obj
        (correspondenceIncidenceRightPulledStalkModule f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t)) =
    Module.length
      ((correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)).presheaf.stalk t)
      ((correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)).presheaf.stalk t) := by
  rw [(correspondencePulledStalkTorZeroIso_graph_right f g h z ψ hψ s t).toLinearEquiv.length_eq]
  let inc := correspondenceIncidenceInclusion f g h z (correspondenceGraphMap g h ψ hψ s.val)
  let q := (inc.stalkMap t).hom
  let A := (correspondenceIncidence f g h z
    (correspondenceGraphMap g h ψ hψ s.val)).presheaf.stalk t
  let M := ModuleCat.of A A
  let := q.toAlgebra
  let : IsScalarTower ((correspondenceTripleProduct f g h).presheaf.stalk (inc t)) A
      ((ModuleCat.restrictScalars q).obj M) := ⟨fun r a m => by
    change (q r * a) • m = q r • (a • m)
    exact mul_smul (q r) a m⟩
  exact Module.length_eq_of_surjective (R := A)
    (M := (ModuleCat.restrictScalars q).obj M) (inc.stalkMap_surjective t)

/-- At an actual generic incidence point, degree-zero length is one because the
incidence is open in the original integral support and therefore reduced. -/
theorem length_correspondencePulledStalkTor_zero_graph_right_eq_one
    (t : correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val))
    (ht : IsMax t) :
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z
        (correspondenceGraphMap g h ψ hψ s.val) t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
        (correspondenceIncidenceInclusion f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t))) 0).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t)).obj
        (correspondenceIncidenceRightPulledStalkModule f g h z
          (correspondenceGraphMap g h ψ hψ s.val) t)) = 1 := by
  rw [length_correspondencePulledStalkTor_zero_graph_right f g h z ψ hψ s t]
  have := isOpenImmersion_correspondenceIncidence_fst_graphMap f g h ψ hψ z s
  have : IsReduced
      (correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val)) :=
    isReduced_of_isOpenImmersion (pullback.fst
      ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt (correspondenceGraphMap g h ψ hψ s.val)).subschemeι ≫
        pullback.fst g h))
  exact length_stalk_eq_one_of_isMax ht

end Graph

end Stacks.Chow

namespace Stacks.Chow

section IdentityOverField

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [IsSeparated g] [IsLocallyNoetherian Y] [IsNormal Y]
  (z : pullback (C := Scheme) f g) (s : genericPoints Y)

/-- Every right identity component over an arbitrary field has zero positive
actual pulled-support Tor. The outer projection's flatness is inferred, not assumed. -/
theorem isZero_correspondencePulledStalkTor_succ_identity_right
    (t : correspondenceIncidence f g g z (correspondenceGraphMap g g (𝟙 Y) (by simp) s.val))
    (n : ℕ) :
    IsZero (((Tor (ModuleCat ((correspondenceTripleProduct f g g).presheaf.stalk
      (correspondenceIncidenceInclusion f g g z
        (correspondenceGraphMap g g (𝟙 Y) (by simp) s.val) t))) (n + 1)).obj
      (correspondenceIncidenceLeftPulledStalkModule f g g z
        (correspondenceGraphMap g g (𝟙 Y) (by simp) s.val) t)).obj
      (correspondenceIncidenceRightPulledStalkModule f g g z
        (correspondenceGraphMap g g (𝟙 Y) (by simp) s.val) t)) :=
  isZero_correspondencePulledStalkTor_succ_graph_right f g g z (𝟙 Y) (by simp) s t n

end IdentityOverField

end Stacks.Chow

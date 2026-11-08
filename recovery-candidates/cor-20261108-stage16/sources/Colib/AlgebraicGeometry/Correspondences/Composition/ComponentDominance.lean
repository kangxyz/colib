/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Incidence
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversallyOpen.QuasiFiniteDominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Open.Generizing
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# Every generic incidence component covers the source component

For actual integral finite-correspondence supports `A` and `B`, over a locally
Noetherian normal middle scheme, the projection `A ×[Y] B → A` is universally open
and finite. Consequently every generic point of the incidence maps to the generic
point of `A`, and its integral closed subscheme covers exactly the source component
covered by `A`.

This is the integral-source application in the proof of
Mazza--Voevodsky--Weibel, Lemma 1.7, printed page 5. No integrality or connectedness
of the ambient source or middle schemes is imposed. No flatness of the finite
supports is assumed. The claim concerns the genuine incidence scheme and native
`integralComponentAt`, before any Tor multiplicity or cycle is assigned.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- A generic point of the actual incidence projects to a generic point of the
first integral support. No flatness of either finite support is required. -/
theorem mem_genericPoints_correspondenceIncidenceFst
    [IsNormal Y] [IsLocallyNoetherian Y]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w)
    (ht : t ∈ genericPoints (correspondenceIncidence f g h z w)) :
    pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt w).subschemeι ≫ pullback.fst g h) t ∈
        genericPoints (integralComponentAt z).subscheme := by
  let a := (integralComponentAt z).subschemeι ≫ pullback.snd f g
  let b := (integralComponentAt w).subschemeι ≫ pullback.fst g h
  let p : correspondenceIncidence f g h z w ⟶ (integralComponentAt z).subscheme :=
    pullback.fst a b
  let : IsIntegral (integralComponentAt w).subscheme := isIntegral_integralComponentAt w
  let : IsFinite b := hw.1
  let : UniversallyOpen b := by
    apply universallyOpen_of_locallyQuasiFinite_of_dominant_components b
      isGeometricallyUnibranch_of_isNormal
    intro C
    have hC : (C : Set (integralComponentAt w).subscheme) = Set.univ := by
      simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using C.2
    refine ⟨⟨Set.range b, hw.2⟩, ?_⟩
    rw [hC, Set.image_univ]
    exact b.isClosedMap.isClosed_range.closure_eq
  exact mem_genericPoints_of_generalizingMap
    ((liftsGeneralizations_iff_generalizingMap p).mp
      (liftsGeneralizations_of_isOpenMap p p.isOpenMap)) ht

set_option backward.isDefEq.respectTransparency false in
/-- There are finitely many generic incidence components: all lie over the single
first-support generic point, whose fibre is finite. This needs no global
Noetherianness or quasi-compactness of the ambient source schemes. -/
theorem finite_genericPoints_correspondenceIncidence
    [IsNormal Y] [IsLocallyNoetherian Y]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hw : IsFiniteCorrespondencePoint g h w) :
    (genericPoints (correspondenceIncidence f g h z w)).Finite := by
  let a := (integralComponentAt z).subschemeι ≫ pullback.snd f g
  let b := (integralComponentAt w).subschemeι ≫ pullback.fst g h
  let p : correspondenceIncidence f g h z w ⟶ (integralComponentAt z).subscheme :=
    pullback.fst a b
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  let : IsFinite b := hw.1
  refine (p.finite_preimage_singleton (genericPoint (integralComponentAt z).subscheme)).subset ?_
  intro t ht
  have hgt := mem_genericPoints_correspondenceIncidenceFst f g h z w hw t ht
  simpa only [genericPoints_eq_singleton, Set.mem_preimage, Set.mem_singleton_iff] using hgt

set_option backward.isDefEq.respectTransparency false in
/-- Every generic incidence component has precisely the first support's source image. -/
theorem range_integralComponent_correspondenceIncidenceLeft
    [IsNormal Y] [IsLocallyNoetherian Y]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w)
    (ht : t ∈ genericPoints (correspondenceIncidence f g h z w)) :
    Set.range ((integralComponentAt t).subschemeι ≫
      correspondenceIncidenceLeft f g h z w) =
      Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) := by
  let a := (integralComponentAt z).subschemeι ≫ pullback.snd f g
  let b := (integralComponentAt w).subschemeι ≫ pullback.fst g h
  let p : correspondenceIncidence f g h z w ⟶ (integralComponentAt z).subscheme :=
    pullback.fst a b
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  let : IsFinite b := hw.1
  have hgt := mem_genericPoints_correspondenceIncidenceFst f g h z w hw t ht
  have heq : p t = genericPoint (integralComponentAt z).subscheme := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hgt
  have hp : Set.range ((integralComponentAt t).subschemeι ≫ p) = Set.univ := by
    change Set.range (p ∘ (integralComponentAt t).subschemeι) = _
    rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι,
      coe_support_integralComponentAt,
      ← p.isClosedMap.closure_image_eq_of_continuous p.continuous,
      Set.image_singleton, heq]
    exact genericPoint_spec (integralComponentAt z).subscheme
  change Set.range (((integralComponentAt z).subschemeι ≫ pullback.fst f g) ∘
    ((integralComponentAt t).subschemeι ≫ p)) = _
  rw [Set.range_comp, hp, Set.image_univ]

/-- Normality of the middle scheme supplies the actual admissible source component
for every generic point of the incidence scheme. -/
theorem range_integralComponent_correspondenceIncidenceLeft_mem
    [IsNormal Y] [IsLocallyNoetherian Y]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w)
    (ht : t ∈ genericPoints (correspondenceIncidence f g h z w)) :
    Set.range ((integralComponentAt t).subschemeι ≫
      correspondenceIncidenceLeft f g h z w) ∈ irreducibleComponents X := by
  rw [range_integralComponent_correspondenceIncidenceLeft f g h z w hw t ht]
  exact hz.2

/-- Over any field, smoothness of the actual middle scheme supplies normality and
local Noetherianness for generic incidence component dominance. -/
theorem range_integralComponent_correspondenceIncidenceLeft_mem_of_smooth
    {k : Type u} [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
    [Smooth g]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w)
    (ht : t ∈ genericPoints (correspondenceIncidence f g h z w)) :
    Set.range ((integralComponentAt t).subschemeι ≫
      correspondenceIncidenceLeft f g h z w) ∈ irreducibleComponents X := by
  let : IsNormal Y := isNormal_of_isRegular Y (isRegular_of_smooth_over_field g)
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  exact range_integralComponent_correspondenceIncidenceLeft_mem f g h z w hz hw t ht

end Stacks.Chow

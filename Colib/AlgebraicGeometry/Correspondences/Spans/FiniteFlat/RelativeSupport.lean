/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Basic

/-! # The whole support correspondence on an actual relative product -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme

/-- Finiteness is preserved by equality of the actual source map. -/
theorem isFinite_of_spanLeg_eq {D X : Scheme.{u}} {f g : D ⟶ X}
    (h : f = g) (hg : IsFinite g) : IsFinite f := h.symm ▸ hg

/-- Flatness is preserved by equality of the actual source map. -/
theorem flat_of_spanLeg_eq {D X : Scheme.{u}} {f g : D ⟶ X}
    (h : f = g) (hg : Flat g) : Flat f := h.symm ▸ hg

/-- The source of a finite span leg over a Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_finite_spanLeg {D X : Scheme.{u}} [IsNoetherian X]
    (f : D ⟶ X) (hf : IsFinite f) : IsNoetherian D :=
  letI : IsFinite f := hf
  isNoetherian_of_finiteType_of_isNoetherian f

/-- The two literal legs of a whole relative support commute over the ground base. -/
theorem relativeSupport_legs_over_base {X Y S T : Scheme.{u}}
    (q : X ⟶ S) (r : Y ⟶ S) (t : S ⟶ T) (I : (pullback q r).IdealSheafData) :
    (I.subschemeι ≫ pullback.fst q r) ≫ (q ≫ t) =
      (I.subschemeι ≫ pullback.snd q r) ≫ (r ≫ t) := by
  simp only [Category.assoc, pullback.condition_assoc]

/-- Both properties of the actual base-changed source leg pass through an
isomorphism preserving that leg. -/
theorem finiteFlat_of_cartesian_support_iso {A B D E : Scheme.{u}}
    (i : A ⟶ B) (f : D ⟶ B) (g : E ⟶ A) (e : pullback i f ≅ E)
    (h : e.hom ≫ g = pullback.fst i f) (hf : IsFinite f) (hflat : Flat f) :
    IsFinite g ∧ Flat g := by
  let : IsFinite f := hf
  let : Flat f := hflat
  have he : g = e.inv ≫ pullback.fst i f := by
    rw [← h, Iso.inv_hom_id_assoc]
  exact ⟨isFinite_of_spanLeg_eq he inferInstance, flat_of_spanLeg_eq he inferInstance⟩

/-- The same full finite-flat span, using its literal scheme structure maps. -/
def ofFiniteFlatSpanRaw {S X Y D : Scheme.{u}} [IsNoetherian X]
    (a : X ⟶ S) (b : Y ⟶ S) [IsSeparated b] [LocallyOfFiniteType b]
    (f : D ⟶ X) [hFin : IsFinite f] [hFlat : Flat f]
    (g : D ⟶ Y) (h : f ≫ a = g ≫ b) :
    finiteCorrespondences a b :=
  letI := isNoetherian_of_finiteType_of_isNoetherian f
  let m := pullback.lift f g h
  let hm : m ≫ pullback.fst a b = f := pullback.lift_fst f g h
  letI : IsFinite (m ≫ pullback.fst a b) := isFinite_of_spanLeg_eq hm hFin
  letI : Flat (m ≫ pullback.fst a b) := flat_of_spanLeg_eq hm hFlat
  letI : IsFinite m := IsFinite.of_comp m (pullback.fst a b)
  finiteFlatSpanFundamental a b m

/-- The paired support span whose original finite-flat source leg is specified
by its projection equality. -/
def finiteFlatSpanFromAmbientLegRaw {S X Y D : Scheme.{u}} [IsNoetherian X]
    (a : X ⟶ S) (b : Y ⟶ S) [IsSeparated b] [LocallyOfFiniteType b]
    (m : D ⟶ pullback a b) [IsFinite m] (f : D ⟶ X)
    (hf : m ≫ pullback.fst a b = f) (hFin : IsFinite f) (hFlat : Flat f) :
    finiteCorrespondences a b :=
  letI : IsFinite f := hFin
  letI : IsNoetherian D := isNoetherian_of_finiteType_of_isNoetherian f
  letI : IsFinite (m ≫ pullback.fst a b) := isFinite_of_spanLeg_eq hf hFin
  letI : Flat (m ≫ pullback.fst a b) := flat_of_spanLeg_eq hf hFlat
  finiteFlatSpanFundamental a b m

/-- The whole finite-flat span of a closed support on the actual relative product. -/
def relativeSupportSpan {k : Type u} [Field k] {U V : SmoothSite (Spec (.of k))}
    {S : Scheme.{u}} (b : U.left ⟶ S) (r : V.left ⟶ S)
    (J : (pullback b r).IdealSheafData)
    [IsFinite (J.subschemeι ≫ pullback.fst b r)] [Flat (J.subschemeι ≫ pullback.fst b r)]
    (h : pullback.fst b r ≫ U.hom = pullback.snd b r ≫ V.hom) :
    Cor.mk U ⟶ Cor.mk V :=
  ofFiniteFlatSpan (X := U) (Y := V) (J.subschemeι ≫ pullback.fst b r)
    (J.subschemeι ≫ pullback.snd b r) (by simp only [Category.assoc, h])

end AlgebraicGeometry.Cor

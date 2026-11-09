/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteSplitting
public import Colib.AlgebraicGeometry.Sites.Nisnevich.Lifting.QuasiFinite
public import Colib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteEtaleNeighborhoodIso
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap

/-!
# Lifting a finite support with one distinguished branch

The support may have nilpotents and arbitrary residue-field extensions over
the base. The isomorphism-neighborhood argument is applied over the support,
and finite closed-image removal then shrinks the original base.

Implementation adapted from
`Motivic/Aglib/AlgebraicGeometry/Sites/Nisnevich/Lifting/FiniteBranchLift.lean`
at motivic commit a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A separated étale lift of the unique point of a finite fiber extends to
the entire pulled-back finite support over a genuine pointed Nisnevich
neighborhood. No flatness or reducedness of the finite support is required. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Nisnevich/Lifting/FiniteBranchLift.lean:112-229"
  "adaptation" "Pointed etale lift of the whole finite singleton branch with its exact point"]
theorem exists_nisnevich_lift_of_isFinite_singleton_with_point
    {Z V S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p]
    (s : S) (z : Z) (hz : p z = s)
    (huniq : ∀ z' : Z, p z' = s → z' = z)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (v : V) (hv : q v = z) (hres : IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback p g ⟶ V, b ≫ q = pullback.fst p g ∧
      ∀ t : (pullback p g : Scheme), pullback.snd p g t = u → b t = v := by
  obtain ⟨U, g, hg, u, hu, hgu, E, _, e, _, hE, hev, heu, hEuniq⟩ :=
    exists_nisnevich_isCompl_of_quasiFiniteAt (q ≫ p)
      (by simpa only [Scheme.Hom.comp_apply, hv] using hz)
      ((q ≫ p).quasiFiniteAt v)
  change ↥E.toScheme at e
  let r : pullback (q ≫ p) g ⟶ pullback p g :=
    (pullbackRightPullbackFstIso p g q).inv ≫ pullback.snd q (pullback.fst p g)
  have hr₁ : r ≫ pullback.fst p g = pullback.fst (q ≫ p) g ≫ q := by simp [r]
  have hr₂ : r ≫ pullback.snd p g = pullback.snd (q ≫ p) g := by simp [r]
  have : Etale r := by dsimp [r]; infer_instance
  let a : E.toScheme ⟶ pullback p g := E.ι ≫ r
  have ha₂ : a ≫ pullback.snd p g = E.ι ≫ pullback.snd (q ≫ p) g := by
    simp [a, hr₂]
  have ha₁ : a ≫ pullback.fst p g = E.ι ≫ pullback.fst (q ≫ p) g ≫ q := by
    simp [a, hr₁]
  have : IsFinite (a ≫ pullback.snd p g) := by rw [ha₂]; exact hE
  have : IsFinite a := .of_comp a (pullback.snd p g)
  have hae : pullback.snd p g (a e) = u := by
    rw [← Scheme.Hom.comp_apply, ha₂]
    exact heu
  have hpa : pullback.fst p g (a e) = z := by
    rw [← Scheme.Hom.comp_apply, ha₁]
    change q (pullback.fst (q ≫ p) g e.1) = z
    rwa [hev]
  have htuniq : ∀ t : (pullback p g : Scheme), pullback.snd p g t = u → t = a e := by
    intro t ht
    apply pullback_point_ext_of_isIso_residueFieldMap p g t (a e) ?_
      (ht.trans hae.symm) (by rw [hae]; exact hgu)
    rw [hpa]
    apply huniq
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ht, hu]
  have haeuniq : ∀ e' : E, a e' = a e → e' = e := by
    intro e' he'
    apply hEuniq
    have he'' := congrArg (pullback.snd p g) he'
    change (a ≫ pullback.snd p g) e' = (a ≫ pullback.snd p g) e at he''
    rw [ha₂] at he''
    exact he''.trans heu
  have hleft := isIso_residueFieldMap_pullback_fst_of_right (q ≫ p) g e.1
    (by rw [heu]; exact hgu)
  have hfirst := isIso_residueFieldMap_pullback_fst_of_right p g (a e)
    (by rw [hae]; exact hgu)
  have hq : IsIso (q.residueFieldMap (pullback.fst (q ≫ p) g e.1)) := by
    rw [hev]
    exact hres
  have hcomp : IsIso ((a ≫ pullback.fst p g).residueFieldMap e) := by
    rw [ha₁, Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
    change IsIso (q.residueFieldMap (pullback.fst (q ≫ p) g e.1) ≫
      (pullback.fst (q ≫ p) g).residueFieldMap e.1 ≫ E.ι.residueFieldMap e)
    exact IsIso.comp_isIso' hq (IsIso.comp_isIso' hleft
      (Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion (f := E.ι) (x := e)))
  rw [Scheme.residueFieldMap_comp] at hcomp
  have hares : IsIso (a.residueFieldMap e) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _
      ((pullback.fst p g).residueFieldMap (a e)) _ hfirst hcomp
  obtain ⟨O, heO, hO⟩ := a.exists_isIso_morphismRestrict_of_singleton
    (a e) e rfl haeuniq hares
  obtain ⟨W, huW, hW⟩ := exists_open_preimage_disjoint_of_isFinite (pullback.snd p g)
    (O : Set (pullback p g : Scheme))ᶜ O.isOpen.isClosed_compl u (by
      intro t ht htu
      exact ht ((htuniq t htu) ▸ heO))
  let g' : W.toScheme ⟶ S := W.ι ≫ g
  let k : pullback p g' ⟶ pullback p g :=
    pullback.map p g' p g (𝟙 Z) W.ι (𝟙 S) (by simp) (by simp [g'])
  have hk : Set.range k ⊆ Set.range O.ι := by
    rintro t ⟨t', rfl⟩
    rw [Scheme.Opens.range_ι]
    by_contra hn
    apply Set.disjoint_left.mp hW ?_ hn
    change pullback.snd p g (k t') ∈ W
    have hk₂ : k ≫ pullback.snd p g = pullback.snd p g' ≫ W.ι := by simp [k]
    have hpoint : pullback.snd p g (k t') = W.ι (pullback.snd p g' t') :=
      congrArg (fun f : pullback p g' ⟶ U ↦ f t') hk₂
    exact hpoint.symm ▸ (show W.ι (pullback.snd p g' t') ∈ W from
      (pullback.snd p g' t').property)
  let l : pullback p g' ⟶ O.toScheme := IsOpenImmersion.lift O.ι k hk
  have hl : l ≫ O.ι = k := IsOpenImmersion.lift_fac O.ι k hk
  let b : pullback p g' ⟶ V :=
    l ≫ inv (a ∣_ O) ≫ (a ⁻¹ᵁ O).ι ≫ E.ι ≫ pullback.fst (q ≫ p) g
  let bE : pullback p g' ⟶ E.toScheme := l ≫ inv (a ∣_ O) ≫ (a ⁻¹ᵁ O).ι
  have hbE : bE ≫ a = k := by
    change l ≫ inv (a ∣_ O) ≫ (a ⁻¹ᵁ O).ι ≫ a = k
    rw [← morphismRestrict_ι]
    simp only [IsIso.inv_hom_id_assoc]
    exact hl
  let w : W.toScheme := ⟨u, huW⟩
  refine ⟨W, g', inferInstance, w, hu, ?_, b, ?_, ?_⟩
  · rw [Scheme.residueFieldMap_comp W.ι g w]
    exact IsIso.comp_isIso' hgu
      (Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion (f := W.ι) (x := w))
  · change l ≫ inv (a ∣_ O) ≫ (a ⁻¹ᵁ O).ι ≫ E.ι ≫
      pullback.fst (q ≫ p) g ≫ q = pullback.fst p g'
    rw [← ha₁, ← Category.assoc (a ⁻¹ᵁ O).ι a,
      ← morphismRestrict_ι]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc, hl]
    simp [k]
  · intro t ht
    have hk₂ : k ≫ pullback.snd p g = pullback.snd p g' ≫ W.ι := by simp [k]
    have hkt : pullback.snd p g (k t) = u := by
      have h := congrArg (fun f : pullback p g' ⟶ U ↦ f t) hk₂
      change pullback.snd p g (k t) = W.ι (pullback.snd p g' t) at h
      rw [ht] at h
      exact h
    have hbEt : bE t = e := by
      apply haeuniq
      exact (congrArg (fun f : pullback p g' ⟶ pullback p g ↦ f t) hbE).trans
        (htuniq (k t) hkt)
    change pullback.fst (q ≫ p) g (E.ι (bE t)) = v
    rw [hbEt]
    exact hev

/-- The original whole-support lifting endpoint, projected from the same
construction that also preserves the exact input residue-field lift. -/
theorem exists_nisnevich_lift_of_isFinite_singleton
    {Z V S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p]
    (s : S) (z : Z) (hz : p z = s)
    (huniq : ∀ z' : Z, p z' = s → z' = z)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (v : V) (hv : q v = z) (hres : IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback p g ⟶ V, b ≫ q = pullback.fst p g := by
  obtain ⟨U, g, hg, u, hu, hr, b, hb, _⟩ :=
    exists_nisnevich_lift_of_isFinite_singleton_with_point p s z hz huniq q v hv hres
  exact ⟨U, g, hg, u, hu, hr, b, hb⟩

end AlgebraicGeometry

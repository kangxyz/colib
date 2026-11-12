/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Restrict

/-!
# Exact native frame gluing on the full disjoint boundary

The two boundary frames are glued with their literal restriction equations.
Compatibility follows from disjointness, not from a supplied matching-family
hypothesis. The module is the actual pullback along the coproduct map.

Adapted from the original `Modules/Invertible/Frames/DisjointBoundary/Basic.lean`,
`Restriction.lean`, and `Trivialization.lean` (the latter blob
`2a70e0c954a661fffe68183fe73a306885fd3fd8`) at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
The native pinned module-morphism gluing theorem replaces the old Aglib
internal-Hom construction entirely.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

private theorem sections_empty_ext {X : Scheme.{u}} (M : X.Modules)
    (s t : Γ(M, (⊥ : X.Opens))) : s = t := by
  let A : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  apply A.eq_of_locally_eq' (fun _ : Empty => ⊥) ⊥
    (fun i => nomatch i) (by simp)
  intro i
  exact i.elim

/-- Disjoint open restrictions glue uniquely, without any compatibility input. -/
theorem existsUnique_hom_of_disjoint_restrictions {X : Scheme.{u}} {ι : Type u}
    (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
    (hdisj : Pairwise fun i j => Disjoint (a i).opensRange (a j).opensRange)
    (M N : X.Modules) (e : ∀ i, M.restrict (a i) ⟶ N.restrict (a i)) :
    ∃! E : M ⟶ N, ∀ i, (Modules.restrictFunctor (a i)).map E = e i := by
  have hc : ⨆ i, a i ''ᵁ (⊤ : (Y i).Opens) = ⊤ := by
    apply eq_top_iff.2
    intro x _
    obtain ⟨i, y, rfl⟩ := hcover x
    exact Opens.mem_iSup.2 ⟨i, ⟨y, trivial, rfl⟩⟩
  apply existsUnique_hom_of_restrict_cover a hc e
  intro i j W₁ W₂ V h₁ h₂
  by_cases hij : i = j
  · subst j
    exact localApp_congr (a i) (e i) h₁ h₂
  · have hVi : V ≤ (a i).opensRange := by
      rw [← h₁, ← Scheme.Hom.image_top_eq_opensRange]
      exact Scheme.Hom.image_mono _ le_top
    have hVj : V ≤ (a j).opensRange := by
      rw [← h₂, ← Scheme.Hom.image_top_eq_opensRange]
      exact Scheme.Hom.image_mono _ le_top
    have hV : V = ⊥ := le_bot_iff.1 ((le_inf hVi hVj).trans
      (disjoint_iff.1 (hdisj hij)).le)
    have : Subsingleton Γ(N, V) := by
      rw [hV]
      exact ⟨sections_empty_ext N⟩
    ext s
    exact Subsingleton.elim _ _

/-- Exact isomorphisms on disjoint components glue, including their inverses. -/
theorem exists_iso_of_disjoint_restrictions {X : Scheme.{u}} {ι : Type u}
    (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
    (hdisj : Pairwise fun i j => Disjoint (a i).opensRange (a j).opensRange)
    (M N : X.Modules) (e : ∀ i, M.restrict (a i) ≅ N.restrict (a i)) :
    ∃ E : M ≅ N, ∀ i, (Modules.restrictFunctor (a i)).map E.hom = (e i).hom := by
  obtain ⟨g, hg, -⟩ := existsUnique_hom_of_disjoint_restrictions
    Y a hcover hdisj M N (fun i => (e i).hom)
  obtain ⟨h, hh, -⟩ := existsUnique_hom_of_disjoint_restrictions
    Y a hcover hdisj N M (fun i => (e i).inv)
  have hgh : g ≫ h = 𝟙 M := by
    apply (existsUnique_hom_of_disjoint_restrictions Y a hcover hdisj M M
      (fun i => 𝟙 (M.restrict (a i)))).unique
    · intro i
      rw [Functor.map_comp, hg, hh, Iso.hom_inv_id]
    · intro i
      exact CategoryTheory.Functor.map_id _ _
  have hhg : h ≫ g = 𝟙 N := by
    apply (existsUnique_hom_of_disjoint_restrictions Y a hcover hdisj N N
      (fun i => 𝟙 (N.restrict (a i)))).unique
    · intro i
      rw [Functor.map_comp, hh, hg, Iso.inv_hom_id]
    · intro i
      exact CategoryTheory.Functor.map_id _ _
  exact ⟨⟨g, h, hgh, hhg⟩, hg⟩

variable {D Z C : Scheme.{u}} (i : D ⟶ C) (j : Z ⟶ C)

/-- The first component of the actual boundary pullback. -/
def boundaryCoprodRestrictLeft :
    Modules.pullback (coprod.desc i j) ⋙ Modules.restrictFunctor
        (coprod.inl : D ⟶ D ⨿ Z) ≅ Modules.pullback i :=
  Functor.isoWhiskerLeft _ (Modules.restrictFunctorIsoPullback _) ≪≫
    Modules.pullbackComp _ _ ≪≫ Modules.pullbackCongr (coprod.inl_desc i j)

/-- The second component retains the complete marked scheme. -/
def boundaryCoprodRestrictRight :
    Modules.pullback (coprod.desc i j) ⋙ Modules.restrictFunctor
        (coprod.inr : Z ⟶ D ⨿ Z) ≅ Modules.pullback j :=
  Functor.isoWhiskerLeft _ (Modules.restrictFunctorIsoPullback _) ≪≫
    Modules.pullbackComp _ _ ≪≫ Modules.pullbackCongr (coprod.inr_desc i j)

/-- The infinity frame and the marked-coordinate frame glue on the original
coproduct boundary, with their exact comparison equations. -/
theorem exists_boundaryCoprod_frame (M : C.Modules)
    (eD : (Modules.pullback i).obj M ≅ SheafOfModules.unit D.ringCatSheaf)
    (eZ : (Modules.pullback j).obj M ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ∃ E : (Modules.pullback (coprod.desc i j)).obj M ≅
        SheafOfModules.unit (D ⨿ Z).ringCatSheaf,
      (Modules.restrictFunctor (coprod.inl : D ⟶ D ⨿ Z)).map E.hom ≫
          (Modules.restrictUnitIso _).hom =
        (boundaryCoprodRestrictLeft i j).hom.app M ≫ eD.hom ∧
      (Modules.restrictFunctor (coprod.inr : Z ⟶ D ⨿ Z)).map E.hom ≫
          (Modules.restrictUnitIso _).hom =
        (boundaryCoprodRestrictRight i j).hom.app M ≫ eZ.hom := by
  let A : ULift.{u} Bool → Scheme.{u} := fun b => cond b.down D Z
  let a : ∀ b, A b ⟶ D ⨿ Z := fun b => by
    rcases b with ⟨b⟩
    cases b
    · exact coprod.inr
    · exact coprod.inl
  let (b : ULift.{u} Bool) : IsOpenImmersion (a b) := by
    rcases b with ⟨b⟩
    cases b <;> dsimp [a] <;> infer_instance
  let P := (Modules.pullback (coprod.desc i j)).obj M
  let O : (D ⨿ Z).Modules := SheafOfModules.unit (D ⨿ Z).ringCatSheaf
  let e : ∀ b, P.restrict (a b) ≅ O.restrict (a b) := fun b => by
    rcases b with ⟨b⟩
    cases b
    · exact (boundaryCoprodRestrictRight i j).app M ≪≫ eZ ≪≫
        (Modules.restrictUnitIso _).symm
    · exact (boundaryCoprodRestrictLeft i j).app M ≪≫ eD ≪≫
        (Modules.restrictUnitIso _).symm
  obtain ⟨E, hE⟩ := exists_iso_of_disjoint_restrictions A a (by
    intro x
    obtain ⟨x | x, rfl⟩ := (AlgebraicGeometry.coprodMk D Z).surjective x
    · exact ⟨⟨true⟩, x, (AlgebraicGeometry.coprodMk_inl D Z x).symm⟩
    · exact ⟨⟨false⟩, x, (AlgebraicGeometry.coprodMk_inr D Z x).symm⟩) (by
    intro ⟨b⟩ ⟨c⟩ hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact (AlgebraicGeometry.isCompl_opensRange_inl_inr D Z).disjoint.symm
    · exact (AlgebraicGeometry.isCompl_opensRange_inl_inr D Z).disjoint
    · exact (hbc rfl).elim) P O e
  refine ⟨E, ?_, ?_⟩
  · have h := hE ⟨true⟩
    change (Modules.restrictFunctor (coprod.inl : D ⟶ D ⨿ Z)).map E.hom =
      (boundaryCoprodRestrictLeft i j).hom.app M ≫ eD.hom ≫
        (Modules.restrictUnitIso _).inv at h
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · have h := hE ⟨false⟩
    change (Modules.restrictFunctor (coprod.inr : Z ⟶ D ⨿ Z)).map E.hom =
      (boundaryCoprodRestrictRight i j).hom.app M ≫ eZ.hom ≫
        (Modules.restrictUnitIso _).inv at h
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- A prescribed marked scalar and identity on infinity give an actual
whole-boundary unit automorphism, not a compatibility assumption. -/
theorem exists_boundaryCoprod_unitAutomorphism (D Z : Scheme.{u})
    (r : SheafOfModules.unit Z.ringCatSheaf ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ∃ E : SheafOfModules.unit (D ⨿ Z).ringCatSheaf ≅
        SheafOfModules.unit (D ⨿ Z).ringCatSheaf,
      (Modules.restrictFunctor (coprod.inl : D ⟶ D ⨿ Z)).map E.hom = 𝟙 _ ∧
      (Modules.restrictFunctor (coprod.inr : Z ⟶ D ⨿ Z)).map E.hom ≫
        (Modules.restrictUnitIso _).hom = (Modules.restrictUnitIso _).hom ≫ r.hom := by
  let A : ULift.{u} Bool → Scheme.{u} := fun b => cond b.down D Z
  let a : ∀ b, A b ⟶ D ⨿ Z := fun b => by
    rcases b with ⟨b⟩
    cases b
    · exact coprod.inr
    · exact coprod.inl
  let (b : ULift.{u} Bool) : IsOpenImmersion (a b) := by
    rcases b with ⟨b⟩
    cases b <;> dsimp [a] <;> infer_instance
  let O : (D ⨿ Z).Modules := SheafOfModules.unit (D ⨿ Z).ringCatSheaf
  let e : ∀ b, O.restrict (a b) ≅ O.restrict (a b) := fun b => by
    rcases b with ⟨b⟩
    cases b
    · exact Modules.restrictUnitIso _ ≪≫ r ≪≫ (Modules.restrictUnitIso _).symm
    · exact Iso.refl _
  obtain ⟨E, hE⟩ := exists_iso_of_disjoint_restrictions A a (by
    intro x
    obtain ⟨x | x, rfl⟩ := (AlgebraicGeometry.coprodMk D Z).surjective x
    · exact ⟨⟨true⟩, x, (AlgebraicGeometry.coprodMk_inl D Z x).symm⟩
    · exact ⟨⟨false⟩, x, (AlgebraicGeometry.coprodMk_inr D Z x).symm⟩) (by
    intro ⟨b⟩ ⟨c⟩ hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact (AlgebraicGeometry.isCompl_opensRange_inl_inr D Z).disjoint.symm
    · exact (AlgebraicGeometry.isCompl_opensRange_inl_inr D Z).disjoint
    · exact (hbc rfl).elim) O O e
  refine ⟨E, hE ⟨true⟩, ?_⟩
  have h := hE ⟨false⟩
  change (Modules.restrictFunctor (coprod.inr : Z ⟶ D ⨿ Z)).map E.hom =
    (Modules.restrictUnitIso _).hom ≫ r.hom ≫ (Modules.restrictUnitIso _).inv at h
  apply (Iso.eq_comp_inv (Modules.restrictUnitIso
    (coprod.inr : Z ⟶ D ⨿ Z))).mp
  simpa only [Category.assoc] using h

end AlgebraicGeometry.Scheme.RelativeCurvePencil

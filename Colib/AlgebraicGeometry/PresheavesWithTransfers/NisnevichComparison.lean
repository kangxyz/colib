/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Basic
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphSingleton
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.DisjointUnions
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteDescent
public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.LocalExactness
public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Topology

/-!
# Comparison of actual correspondence and ordinary Nisnevich sheaf conditions

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Presheaf/NisnevichComparison.lean`, blob
`45418deb4609a06d5a1068eb2356b6c208361b42`.
The reverse implication uses proved local signed Cech boundaries and additivity;
no fullness or continuity of the graph functor on arbitrary presheaves is asserted.
The independent singleton and disjoint-union comparisons have separate owners.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Actual local Čech exactness upgrades scheme Čech compatibility to
compatibility for all signed correspondences with the same image. -/
theorem correspondence_compatible_of_cech_compatible
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] (E : AddCommGrpCat.{v})
    (hF : ∀ {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X),
      Etale q.left → (∀ x : X.left, ∃ y : Y.left,
        q.left y = x ∧ IsIso (q.left.residueFieldMap y)) →
      Function.Injective (fun s : E ⟶ F.obj (op (Cor.mk X)) =>
        s ≫ F.map ((Cor.graphFunctor k).map q).op))
    {Y V : SmoothSite (Spec (.of k))} (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v))
    (s : E ⟶ F.obj (op (Cor.mk V)))
    (hs : s ≫ F.map ((Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q)).op =
      s ≫ F.map ((Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)).op)
    {X : Cor k} (α β : X ⟶ Cor.mk V)
    (hαβ : α ≫ (Cor.graphFunctor k).map q = β ≫ (Cor.graphFunctor k).map q) :
    s ≫ F.map α.op = s ≫ F.map β.op := by
  apply sections_ext_of_nisnevich_local F E hF
  intro x
  let Γq : Cor.mk V ⟶ Cor.mk Y := (Cor.graphFunctor k).map q
  change α ≫ Γq = β ≫ Γq at hαβ
  have hzero : (α - β) ≫ Γq = 0 := by
    rw [Preadditive.sub_comp, hαβ, sub_self]
  obtain ⟨U, g, hg, u, hu, hgu, δ, hδ⟩ :=
    Cor.exists_nisnevich_cech_boundary k (α - β) q hq hzero x
  refine ⟨U, g, hg, ⟨u, hu, hgu⟩, ?_⟩
  let Γg : Cor.mk U ⟶ X := (Cor.graphFunctor k).map g
  let Γ₁ : Cor.mk (SmoothSite.etalePullback q q) ⟶ Cor.mk V :=
    (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q)
  let Γ₂ : Cor.mk (SmoothSite.etalePullback q q) ⟶ Cor.mk V :=
    (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)
  change Γg ≫ (α - β) = δ ≫ Γ₁ - δ ≫ Γ₂ at hδ
  change s ≫ F.map Γ₁.op = s ≫ F.map Γ₂.op at hs
  change (s ≫ F.map α.op) ≫ F.map Γg.op =
    (s ≫ F.map β.op) ≫ F.map Γg.op
  apply sub_eq_zero.mp
  calc
    (s ≫ F.map α.op) ≫ F.map Γg.op -
        (s ≫ F.map β.op) ≫ F.map Γg.op =
      s ≫ F.map (Γg ≫ (α - β)).op := by
        simp only [op_comp, op_sub, F.map_comp, F.map_sub,
          Preadditive.comp_sub, Category.assoc]
    _ = s ≫ F.map (δ ≫ Γ₁ - δ ≫ Γ₂).op := by rw [hδ]
    _ = 0 := by
      simp only [op_sub, F.map_sub, Preadditive.comp_sub, op_comp, F.map_comp,
        ← Category.assoc]
      rw [hs, sub_self]

/-- For an additive presheaf separated on singleton covers, singleton
Nisnevich descent is equivalent before and after restricting to graph arrows. -/
theorem isSheafFor_graph_singleton_iff
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] (E : AddCommGrpCat.{v})
    (hF : ∀ {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X),
      Etale q.left → (∀ x : X.left, ∃ y : Y.left,
        q.left y = x ∧ IsIso (q.left.residueFieldMap y)) →
      Function.Injective (fun s : E ⟶ F.obj (op (Cor.mk X)) =>
        s ≫ F.map ((Cor.graphFunctor k).map q).op))
    {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X) [Etale q.left]
    (hq : ∀ x : X.left, ∃ y : Y.left,
      q.left y = x ∧ IsIso (q.left.residueFieldMap y)) :
    Presieve.IsSheafFor (F ⋙ coyoneda.obj (op E))
        (Presieve.singleton ((Cor.graphFunctor k).map q)) ↔
      Presieve.IsSheafFor ((Cor.graphFunctor k).op ⋙ F ⋙ coyoneda.obj (op E))
        (Presieve.singleton q) := by
  constructor
  · intro h
    rw [Presieve.isSheafFor_singleton] at h ⊢
    intro s hs
    apply h s
    intro Z α β hαβ
    apply correspondence_compatible_of_cech_compatible F E hF q hq s ?_ α β hαβ
    exact hs (SmoothSite.etalePullbackFst q q) (SmoothSite.etalePullbackSnd q q)
      (SmoothSite.etalePullbackCone q q).condition
  · exact isSheafFor_graph_singleton_of_restriction (F ⋙ coyoneda.obj (op E)) q

/-- A presheaf on actual correspondences is a sheaf for the correspondence
Nisnevich topology exactly when it has descent for genuine singleton graph covers. -/
theorem isSheaf_correspondenceTopology_iff_singletons (F : (Cor k)ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf (Cor.nisnevichTopology k) F ↔
      ∀ {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X), Cor.IsNisnevichCover k q →
        Presieve.IsSheafFor F (Presieve.singleton ((Cor.graphFunctor k).map q)) := by
  constructor
  · intro h X Y q hq
    exact h.isSheafFor _ (Cor.graph_cover_mem_nisnevichTopology k q hq)
  · intro h X R hR
    obtain ⟨V, q, hq, hRq⟩ := hR
    apply (h q hq).of_singleton hRq
    intro Y α _
    obtain ⟨U, g, hg, β, hβ⟩ := Cor.exists_nisnevich_cover_graph_factorization k α q hq
    exact ⟨Cor.mk U, (Cor.graphFunctor k).map g, β, hβ.symm,
      (h g hg).isSeparatedFor⟩

/-- An ordinary Nisnevich sheaf underlying a transfer presheaf is a sheaf for
actual correspondence sieves. This implication does not require additivity. -/
theorem isSheaf_correspondenceTopology_of_restriction
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v})
    (hF : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((Cor.graphFunctor k).op ⋙ F)) :
    Presheaf.IsSheaf (Cor.nisnevichTopology k) F := by
  intro E
  apply (isSheaf_correspondenceTopology_iff_singletons (F ⋙ coyoneda.obj (op E))).mpr
  intro X Y q hq
  apply isSheafFor_graph_singleton_of_restriction
  exact (hF E).isSheafFor_of_mem_precoverage
    ((Cor.isNisnevichCover_iff_singleton_mem k q).mp hq)

/-- A correspondence Nisnevich sheaf which is additive in source arrows
has ordinary descent for each genuine singleton Nisnevich cover. -/
theorem isSheafFor_restriction_singleton_of_correspondenceSheaf
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive]
    (hF : Presheaf.IsSheaf (Cor.nisnevichTopology k) F) (E : AddCommGrpCat.{v})
    {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X) (hq : Cor.IsNisnevichCover k q) :
    Presieve.IsSheafFor ((Cor.graphFunctor k).op ⋙ F ⋙ coyoneda.obj (op E))
      (Presieve.singleton q) := by
  let : Etale q.left := hq.1
  have hsingle : ∀ {A B : SmoothSite (Spec (.of k))} (r : B ⟶ A),
      Cor.IsNisnevichCover k r → Presieve.IsSheafFor (F ⋙ coyoneda.obj (op E))
        (Presieve.singleton ((Cor.graphFunctor k).map r)) :=
    (isSheaf_correspondenceTopology_iff_singletons
      (F ⋙ coyoneda.obj (op E))).mp (hF E)
  apply (isSheafFor_graph_singleton_iff F E ?_ q hq.2).mp (hsingle q hq)
  intro X Y r hr hr'
  exact Presieve.isSeparatedFor_singleton.mp (hsingle r ⟨hr, hr'⟩).isSeparatedFor

/-- Sheafness for actual correspondence Nisnevich sieves agrees with the
ordinary smooth-site Nisnevich sheaf condition for every additive presheaf.
The proof includes arbitrary covering families and the empty smooth scheme. -/
theorem isSheaf_correspondenceTopology_iff_restriction
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] :
    Presheaf.IsSheaf (Cor.nisnevichTopology k) F ↔
      Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((Cor.graphFunctor k).op ⋙ F) := by
  constructor
  · intro hF E
    let : ∀ (X : SmoothSite (Spec (.of k))), IsNoetherian X.left := fun X => by
      let x : X.left ⟶ Spec (.of k) := X.hom
      let : LocallyOfFiniteType x := SmoothSite.locallyOfFiniteType X
      let : QuasiCompact x := inferInstanceAs (QuasiCompact X.hom)
      let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian x
      let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace x
      exact ⟨⟩
    apply (SmoothSite.isSheaf_iff_singleton_of_finiteCoproduct
      ((Cor.graphFunctor k).op ⋙ F ⋙ coyoneda.obj (op E))
      (fun _ Y => finiteCoproduct_sections_bijective F E Y)).mpr
    intro X Y q hq
    exact isSheafFor_restriction_singleton_of_correspondenceSheaf F hF E q
      ((Cor.isNisnevichCover_iff_singleton_mem k q).mpr hq)
  · exact isSheaf_correspondenceTopology_of_restriction F

/-- The project's actual full-subcategory condition for sheaves with transfers
is exactly sheafness on the actual correspondence Nisnevich site. -/
@[colib_tag "COL-0359",
  colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/NisnevichComparison.lean"
  "adaptation" "Comparison of Nisnevich sheaf conditions"]
theorem isNisnevichSheaf_iff_correspondenceTopology (P : PresheafWithTransfers.{v} k) :
    IsNisnevichSheaf k P ↔ Presheaf.IsSheaf (Cor.nisnevichTopology k) P.obj :=
  (isSheaf_correspondenceTopology_iff_restriction P.obj).symm

end AlgebraicGeometry.PresheafWithTransfers

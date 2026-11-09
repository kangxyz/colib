/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Basic
public import Colib.AlgebraicGeometry.Correspondences.Coproducts.Finite

/-!
# Actual graph restriction and disjoint-union descent

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Presheaf/NisnevichComparison.lean`, blob
`45418deb4609a06d5a1068eb2356b6c208361b42`, the independent lower comparisons.
Only the native correspondence category and the stated actual restriction maps
are used. No fullness or general continuity of the graph functor is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

private theorem map_graph_comp (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v})
    {A B C : SmoothSite (Spec (.of k))} (f : A ⟶ B) (g : B ⟶ C) :
    F.map ((Cor.graphFunctor k).map (f ≫ g)).op =
      F.map ((Cor.graphFunctor k).map g).op ≫ F.map ((Cor.graphFunctor k).map f).op := by
  rw [Functor.map_comp, op_comp, F.map_comp]

/-- Sections on the empty smooth scheme vanish for an additive presheaf with
transfers. This supplies the ordinary empty-family sheaf condition. -/
theorem section_eq_zero_of_isEmpty
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive]
    (E : AddCommGrpCat.{v}) (X : Cor k) [IsEmpty X.toSmoothSite.left]
    (s : E ⟶ F.obj (op X)) : s = 0 := by
  have h : (𝟙 (F.obj (op X))) = 0 := by
    rw [← F.map_id]
    have hzero : (𝟙 (op X)) = 0 := by
      exact congrArg Quiver.Hom.op (Cor.hom_eq_zero_of_isEmpty_source k (𝟙 X))
    rw [hzero, F.map_zero]
  simpa only [Category.comp_id, comp_zero] using congrArg (fun f => s ≫ f) h

/-- An additive presheaf takes the actual binary disjoint union to a product
on sections, with the actual graph restriction maps. -/
theorem binaryCoproduct_sections_bijective
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive]
    (E : AddCommGrpCat.{v}) (X Y : Cor k) :
    Function.Bijective (fun s : E ⟶ F.obj (op (Cor.coproduct k X Y)) =>
      (s ≫ F.map (Cor.coproductInl k X Y).op,
        s ≫ F.map (Cor.coproductInr k X Y).op)) := by
  obtain ⟨p, q, hp, hq, hp', hq', htotal⟩ := Cor.exists_coproduct_projections k X Y
  have recover (s : E ⟶ F.obj (op (Cor.coproduct k X Y))) :
      s = (s ≫ F.map (Cor.coproductInl k X Y).op) ≫ F.map p.op +
        (s ≫ F.map (Cor.coproductInr k X Y).op) ≫ F.map q.op := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, ← F.map_add, ← op_add,
      htotal, op_id, F.map_id, Category.comp_id]
  constructor
  · intro s t h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    rw [recover s, recover t, h₁, h₂]
  · rintro ⟨s, t⟩
    refine ⟨s ≫ F.map p.op + t ≫ F.map q.op, ?_⟩
    apply Prod.ext
    · simp only [Preadditive.add_comp, Category.assoc, ← F.map_comp, ← op_comp,
        hp, hq, op_id, op_zero, F.map_id, F.map_zero, Category.comp_id,
        comp_zero, add_zero]
    · simp only [Preadditive.add_comp, Category.assoc, ← F.map_comp, ← op_comp,
        hp', hq', op_id, op_zero, F.map_id, F.map_zero, Category.comp_id,
        comp_zero, zero_add]

/-- The actual finite disjoint union gives a product of section groups.
The zero-component case uses source-arrow additivity at the empty scheme. -/
theorem finiteCoproduct_sections_bijective
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive]
    (E : AddCommGrpCat.{v}) {n : ℕ} (Y : Fin n → SmoothSite (Spec (.of k))) :
    Function.Bijective (fun s : E ⟶ F.obj (op (Cor.mk (SmoothSite.finiteCoproduct Y))) =>
      fun i => s ≫ F.map ((Cor.graphFunctor k).map (SmoothSite.finiteCoproductι Y i)).op) := by
  induction n with
  | zero =>
      constructor
      · intro s t _
        have : IsEmpty (Cor.mk (SmoothSite.finiteCoproduct Y)).toSmoothSite.left :=
          inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
        rw [section_eq_zero_of_isEmpty F E _ s, section_eq_zero_of_isEmpty F E _ t]
      · intro s
        exact ⟨0, funext (fun i => Fin.elim0 i)⟩
  | succ n ih =>
      let Z := SmoothSite.finiteCoproduct (fun i : Fin n => Y i.succ)
      have hb := binaryCoproduct_sections_bijective F E (Cor.mk (Y 0)) (Cor.mk Z)
      constructor
      · intro s t h
        apply hb.injective
        apply Prod.ext
        · exact congrFun h 0
        · apply (ih (fun i : Fin n => Y i.succ)).injective
          funext i
          have hi := congrFun h i.succ
          change s ≫ F.map ((Cor.graphFunctor k).map
            (SmoothSite.finiteCoproductι (fun i : Fin n => Y i.succ) i ≫
              SmoothSite.coproductInr (Y 0) Z)).op =
            t ≫ F.map ((Cor.graphFunctor k).map
            (SmoothSite.finiteCoproductι (fun i : Fin n => Y i.succ) i ≫
              SmoothSite.coproductInr (Y 0) Z)).op at hi
          have hc := map_graph_comp F
            (SmoothSite.finiteCoproductι (fun j : Fin n => Y j.succ) i)
            (SmoothSite.coproductInr (Y 0) Z)
          have hs := congrArg
            (fun m : F.obj (op (Cor.mk (SmoothSite.finiteCoproduct Y))) ⟶
              F.obj (op (Cor.mk (Y i.succ))) => s ≫ m) hc
          have ht := congrArg
            (fun m : F.obj (op (Cor.mk (SmoothSite.finiteCoproduct Y))) ⟶
              F.obj (op (Cor.mk (Y i.succ))) => t ≫ m) hc
          exact (Category.assoc _ _ _).trans
            (hs.symm.trans (hi.trans (ht.trans (Category.assoc _ _ _).symm)))
      · intro s
        obtain ⟨t, ht⟩ := (ih (fun i : Fin n => Y i.succ)).surjective
          (fun i : Fin n => s i.succ)
        obtain ⟨a, ha⟩ := hb.surjective (s 0, t)
        obtain ⟨ha₁, ha₂⟩ := Prod.mk.inj ha
        refine ⟨a, funext (fun i => ?_)⟩
        refine Fin.cases ha₁ (fun j => ?_) i
        change a ≫ F.map ((Cor.graphFunctor k).map
          (SmoothSite.finiteCoproductι (fun i : Fin n => Y i.succ) j ≫
            SmoothSite.coproductInr (Y 0) Z)).op = s j.succ
        have hc := map_graph_comp F
          (SmoothSite.finiteCoproductι (fun i : Fin n => Y i.succ) j)
          (SmoothSite.coproductInr (Y 0) Z)
        have ha := congrArg
          (fun m : F.obj (op (Cor.mk (SmoothSite.finiteCoproduct Y))) ⟶
            F.obj (op (Cor.mk (Y j.succ))) => a ≫ m) hc
        have hb := congrArg (fun z : E ⟶ F.obj (op (Cor.mk Z)) =>
          z ≫ F.map ((Cor.graphFunctor k).map
            (SmoothSite.finiteCoproductι (fun i : Fin n => Y i.succ) j)).op) ha₂
        exact ha.trans ((Category.assoc _ _ _).symm.trans (hb.trans (congrFun ht j)))

/-- Singleton separation implies separation for every actual Nisnevich family,
using a finite total cover and additivity on finite disjoint unions. -/
theorem sections_ext_of_nisnevich_family
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] (E : AddCommGrpCat.{v})
    (hF : ∀ {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X),
      Etale q.left → (∀ x : X.left, ∃ y : Y.left,
        q.left y = x ∧ IsIso (q.left.residueFieldMap y)) →
      Function.Injective (fun s : E ⟶ F.obj (op (Cor.mk X)) =>
        s ≫ F.map ((Cor.graphFunctor k).map q).op))
    {X : SmoothSite (Spec (.of k))} {ι : Type*}
    {Y : ι → SmoothSite (Spec (.of k))} (f : ∀ i, Y i ⟶ X)
    [∀ i, Etale (f i).left]
    (hf : ∀ x : X.left, ∃ (i : ι) (y : (Y i).left),
      (f i).left y = x ∧ IsIso ((f i).left.residueFieldMap y))
    {s t : E ⟶ F.obj (op (Cor.mk X))}
    (h : ∀ i, s ≫ F.map ((Cor.graphFunctor k).map (f i)).op =
      t ≫ F.map ((Cor.graphFunctor k).map (f i)).op) : s = t := by
  let x : X.left ⟶ Spec (.of k) := X.hom
  let : LocallyOfFiniteType x := SmoothSite.locallyOfFiniteType X
  let : QuasiCompact x := inferInstanceAs (QuasiCompact X.hom)
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian x
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace x
  let : IsNoetherian X.left := ⟨⟩
  let N := SmoothSite.normalizeFiniteNisnevichCover f hf
  apply hF N.map inferInstance N.residueFieldLifting
  apply (finiteCoproduct_sections_bijective F E (fun i => Y (N.index i))).injective
  funext i
  change (s ≫ F.map ((Cor.graphFunctor k).map N.map).op) ≫
      F.map ((Cor.graphFunctor k).map (N.inclusion i)).op =
    (t ≫ F.map ((Cor.graphFunctor k).map N.map).op) ≫
      F.map ((Cor.graphFunctor k).map (N.inclusion i)).op
  have hc := (map_graph_comp F (N.inclusion i) N.map).symm.trans
    (congrArg (fun g : Y (N.index i) ⟶ X => F.map ((Cor.graphFunctor k).map g).op)
      (N.inclusion_map i))
  have hs := congrArg (fun m : F.obj (op (Cor.mk X)) ⟶
    F.obj (op (Cor.mk (Y (N.index i)))) => s ≫ m) hc
  have ht := congrArg (fun m : F.obj (op (Cor.mk X)) ⟶
    F.obj (op (Cor.mk (Y (N.index i)))) => t ≫ m) hc
  exact (Category.assoc _ _ _).trans
    (hs.trans ((h (N.index i)).trans (ht.symm.trans (Category.assoc _ _ _).symm)))

/-- Pointwise smooth Nisnevich neighborhoods detect equality once actual
singleton-cover restrictions are injective. -/
theorem sections_ext_of_nisnevich_local
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] (E : AddCommGrpCat.{v})
    (hF : ∀ {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X),
      Etale q.left → (∀ x : X.left, ∃ y : Y.left,
        q.left y = x ∧ IsIso (q.left.residueFieldMap y)) →
      Function.Injective (fun s : E ⟶ F.obj (op (Cor.mk X)) =>
        s ≫ F.map ((Cor.graphFunctor k).map q).op))
    {X : SmoothSite (Spec (.of k))} {s t : E ⟶ F.obj (op (Cor.mk X))}
    (h : ∀ x : X.left, ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X),
      Etale g.left ∧ (∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u)) ∧
      s ≫ F.map ((Cor.graphFunctor k).map g).op =
        t ≫ F.map ((Cor.graphFunctor k).map g).op) : s = t := by
  choose U g hg hu heq using h
  let (x : X.left) : Etale (g x).left := hg x
  exact sections_ext_of_nisnevich_family F E hF g
    (fun x => ⟨x, hu x⟩) heq

end AlgebraicGeometry.PresheafWithTransfers

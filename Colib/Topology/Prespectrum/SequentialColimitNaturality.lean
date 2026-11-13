/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.SequentialColimitStable
public import Colib.Topology.Prespectrum.TelescopeHomotopy

/-!
# Actual maps and whole homotopies on ordinary sequential prespectrum colimits

Strict maps of the original sequences induce actual ordinary-colimit maps, preserving
identities, composition and zero maps. Strictly compatible whole stage homotopies descend
by first currying their interval parameter into a genuine TopCat colimit cocone. Evaluation
then gives the original coherent prespectrum homotopy, with every stage time unchanged.
The original telescope collapse commutes with these actual maps and whole families.
-/
/-!
Implementation provenance: adapted from Quillen at
`SequentialColimitNaturality.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology CategoryTheory.Limits
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum.SequentialColimit
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i) (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))

/-- The actual target-stage arrows form a cocone on the original source sequence. -/
def mapCocone : Cocone (Functor.ofSequence f) where
  pt := prespectrum F g
  ι := NatTrans.ofSequence (fun i ↦ a i ≫ inclusion F g i) (fun i ↦ by
    rw [Functor.ofSequence_map_homOfLE_succ]
    change f i ≫ (a (i + 1) ≫ inclusion F g (i + 1)) = (a i ≫ inclusion F g i) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, ← ha i, Category.assoc, successor_inclusion])

/-- Original strict stage maps descend through the actual ordinary colimit universal property. -/
def map : prespectrum E f ⟶ prespectrum F g := desc E f (mapCocone E f F g a ha)

/-- Every original ordinary stage inclusion is preserved by the actual map. -/
@[simp] theorem inclusion_map (i : ℕ) : inclusion E f i ≫ map E f F g a ha =
    a i ≫ inclusion F g i := inclusion_desc E f _ i

/-- Original ordinary stage inclusions determine every map from the colimit. -/
theorem hom_ext {D : LoopPrespectrum.{u}} {s t : prespectrum E f ⟶ D}
    (h : ∀ i, inclusion E f i ≫ s = inclusion E f i ≫ t) : s = t :=
  (isColimit E f).hom_ext h

/-- The original ordinary colimit map of identity stages is the literal identity. -/
@[simp] theorem map_id :
    map E f E f (fun i ↦ 𝟙 (E i)) (fun i ↦ by simp) = 𝟙 (prespectrum E f) := by
  apply hom_ext E f
  intro i
  rw [inclusion_map]
  simp only [Category.id_comp, Category.comp_id]

variable (G : ℕ → LoopPrespectrum.{u}) (h : ∀ i, G i ⟶ G (i + 1))
    (b : ∀ i, F i ⟶ G i) (hb : ∀ i, b i ≫ h i = g i ≫ b (i + 1))

/-- Composition retains exactly the original composite stage arrows. -/
@[simp] theorem map_comp : map E f F g a ha ≫ map F g G h b hb =
    map E f G h (fun i ↦ a i ≫ b i)
      (fun i ↦ by rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]) := by
  apply hom_ext E f
  intro i
  rw [← Category.assoc, inclusion_map, Category.assoc, inclusion_map, inclusion_map]
  exact (Category.assoc _ _ _).symm

/-- Original pointwise zero stage arrows descend to the literal zero map. -/
@[simp] theorem map_zero :
    map E f F g (fun i ↦ zeroHom (E i) (F i)) (fun i ↦ by
      apply Hom.ext
      funext k
      ext _x
      exact (g i).map_point k) = zeroHom (prespectrum E f) (prespectrum F g) := by
  apply hom_ext E f
  intro i
  rw [inclusion_map]
  apply Hom.ext
  funext k
  ext x
  exact (inclusion F g i).map_point k

/-- The original telescope collapse is strictly natural for these actual stage maps. -/
theorem collapse_naturality : Telescope.map E f F g a ha ≫ collapse F g =
    collapse E f ≫ map E f F g a ha := by
  apply Telescope.hom_ext
  intro k i s x
  exact (congrArg (fun m ↦ m.map k x) (inclusion_map E f F g a ha i)).symm

variable (a' : ∀ i, E i ⟶ F i) (ha' : ∀ i, a' i ≫ g i = f i ≫ a' (i + 1))
    (H : ∀ i, Homotopy (a i) (a' i))
    (hH : ∀ i k s x, (g i).map k ((H i).level k (s, x)) =
      (H (i + 1)).level k (s, (f i).map k x))

include hH in
/-- Curry the entire original stage family before the ordinary topological colimit descent. -/
def homotopyCocone (k : ℕ) : Cocone (levelDiagram E f k) where
  pt := TopCat.of C(unitInterval, (prespectrum F g).space k)
  ι := NatTrans.ofSequence
    (fun i ↦ TopCat.ofHom (ContinuousMap.curry
      ⟨fun z : (E i).space k × unitInterval ↦ (inclusion F g i).map k
        ((H i).level k (z.2, z.1)), by fun_prop⟩))
    (fun i ↦ by
      apply ConcreteCategory.hom_ext
      intro x
      apply ContinuousMap.ext
      intro s
      change (inclusion F g (i + 1)).map k ((H (i + 1)).level k
          (s, ((Functor.ofSequence f).map (homOfLE (Nat.le_succ i))).map k x)) =
        (inclusion F g i).map k ((H i).level k (s, x))
      rw [Functor.ofSequence_map_homOfLE_succ]
      change (inclusion F g (i + 1)).map k ((H (i + 1)).level k
          (s, (f i).map k x)) = (inclusion F g i).map k ((H i).level k (s, x))
      rw [← hH i k s x]
      exact congrArg (fun m ↦ m.map k ((H i).level k (s, x))) (successor_inclusion F g i))

/-- The actual interval-valued ordinary colimit descent. -/
def homotopyFamily (k : ℕ) : C((prespectrum E f).space k,
    C(unitInterval, (prespectrum F g).space k)) :=
  (colimit.desc (levelDiagram E f k) (homotopyCocone E f F g a a' H hH k)).hom

/-- Every stage point retains the complete original homotopy time. -/
theorem homotopyFamily_inclusion (k i : ℕ) (s : unitInterval) (x : (E i).space k) :
    homotopyFamily E f F g a a' H hH k ((inclusion E f i).map k x) s =
      (inclusion F g i).map k ((H i).level k (s, x)) := by
  have h := ConcreteCategory.congr_hom
    (colimit.ι_desc (homotopyCocone E f F g a a' H hH k) i) x
  exact congrArg (fun p : C(unitInterval, (prespectrum F g).space k) ↦ p s) h

/-- Whole strictly compatible original stage homotopies give an actual colimit homotopy. -/
def mapHomotopy : Homotopy (map E f F g a ha) (map E f F g a' ha') where
  level k := ⟨fun z ↦ homotopyFamily E f F g a a' H hH k z.2 z.1,
    (homotopyFamily E f F g a a' H hH k).uncurry.continuous.comp continuous_swap⟩
  at_zero k q := by
    obtain ⟨i, x, rfl⟩ := TopCat.SequentialColimit.exists_mem_stageRange
      (colimit.isColimit (levelDiagram E f k)) q
    change (E i).space k at x
    change homotopyFamily E f F g a a' H hH k ((inclusion E f i).map k x) 0 =
      (map E f F g a ha).map k ((inclusion E f i).map k x)
    rw [homotopyFamily_inclusion, (H i).at_zero]
    exact (congrArg (fun m ↦ m.map k x) (inclusion_map E f F g a ha i)).symm
  at_one k q := by
    obtain ⟨i, x, rfl⟩ := TopCat.SequentialColimit.exists_mem_stageRange
      (colimit.isColimit (levelDiagram E f k)) q
    change (E i).space k at x
    change homotopyFamily E f F g a a' H hH k ((inclusion E f i).map k x) 1 =
      (map E f F g a' ha').map k ((inclusion E f i).map k x)
    rw [homotopyFamily_inclusion, (H i).at_one]
    exact (congrArg (fun m ↦ m.map k x) (inclusion_map E f F g a' ha' i)).symm
  at_point k s := by
    change homotopyFamily E f F g a a' H hH k ((inclusion E f 0).map k ((E 0).point k)) s = _
    rw [homotopyFamily_inclusion, (H 0).at_point]
    exact (inclusion F g 0).map_point k
  comm k s q t := by
    obtain ⟨i, x, rfl⟩ := TopCat.SequentialColimit.exists_mem_stageRange
      (colimit.isColimit (levelDiagram E f k)) q
    change (E i).space k at x
    change homotopyFamily E f F g a a' H hH (k + 1)
        (structureMap E f k ((inclusion E f i).map k x) t) s =
      structureMap F g k (homotopyFamily E f F g a a' H hH k ((inclusion E f i).map k x) s) t
    have hs := structureMap_inclusion E f k i x t
    change structureMap E f k ((inclusion E f i).map k x) t =
      (inclusion E f i).map (k + 1) ((E i).structureMap k x t) at hs
    rw [hs, homotopyFamily_inclusion, homotopyFamily_inclusion, (H i).comm]
    exact (structureMap_inclusion F g k i ((H i).level k (s, x)) t).symm

/-- The full descended family is exactly the original stage family on every inclusion. -/
@[simp] theorem mapHomotopy_inclusion (k i : ℕ) (s : unitInterval) (x : (E i).space k) :
    (mapHomotopy E f F g a ha a' ha' H hH).level k (s, (inclusion E f i).map k x) =
      (inclusion F g i).map k ((H i).level k (s, x)) :=
  homotopyFamily_inclusion E f F g a a' H hH k i s x

/-- Every original homotopy-time slice is its actual ordinary colimit map. -/
theorem mapHomotopy_at (s : unitInterval) :
    (mapHomotopy E f F g a ha a' ha' H hH).at s =
      map E f F g (fun i ↦ (H i).at s) (fun i ↦ by
        apply Hom.ext
        funext k
        ext x
        exact hH i k s x) := by
  apply hom_ext E f
  intro i
  rw [inclusion_map]
  apply Hom.ext
  funext k
  ext x
  exact mapHomotopy_inclusion E f F g a ha a' ha' H hH k i s x

/-- Collapse commutes at every time with the actual telescope and ordinary-colimit families. -/
theorem collapse_mapHomotopy (k : ℕ) (s : unitInterval)
    (q : (Telescope.prespectrum E f).space k) :
    (mapHomotopy E f F g a ha a' ha' H hH).level k (s, (collapse E f).map k q) =
      (collapse F g).map k ((Telescope.mapHomotopy E f F g a a' ha ha' H hH).level k (s, q)) := by
  induction q using Quot.inductionOn with
  | h z =>
    obtain ⟨i, r, x⟩ := z
    exact mapHomotopy_inclusion E f F g a ha a' ha' H hH k i s x

end Topology.LoopPrespectrum.SequentialColimit

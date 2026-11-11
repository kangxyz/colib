/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.TelescopeEventualHomotopy
public import Colib.Topology.Prespectrum.StableEquivalence
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Category.TopCat.SequentialColimit.Compact

/-!
# The original telescope and the actual sequential topological colimit

Levelwise ordinary TopCat colimits form an actual loop prespectrum by descending the
original structure maps. The original telescope maps to it by constant cylinder tracks.
For T1 stages and closed-embedding successor maps, compact-source factorization proves
that this exact map induces bijections on every based homotopy set and therefore on all
signed stable groups. No arbitrary homotopy-colimit functor is postulated.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum.SequentialColimit

/-- Evaluation at an original prespectrum level. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:32"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def levelFunctor (k : ℕ) : LoopPrespectrum.{u} ⥤ TopCat.{u} where
  obj E := E.space k
  map f := TopCat.ofHom (f.map k)

variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- The original topological sequence at each level. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:39"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def levelDiagram (k : ℕ) : ℕ ⥤ TopCat.{u} := Functor.ofSequence f ⋙ levelFunctor k

/-- The literal ordinary TopCat colimit of the level sequence. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:42"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
abbrev levelSpace (k : ℕ) : TopCat.{u} := colimit (levelDiagram E f k)

/-- Its specified point is the image of the original initial point. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:45"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def point (k : ℕ) : levelSpace E f k := colimit.ι (levelDiagram E f k) 0 ((E 0).point k)

/-- Every original stage point is the same specified colimit point. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:48"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem inclusion_point (k i : ℕ) :
    colimit.ι (levelDiagram E f k) i ((E i).point k) = point E f k := by
  have h := ConcreteCategory.congr_hom
    (colimit.w (levelDiagram E f k) (homOfLE (Nat.zero_le i))) ((E 0).point k)
  change colimit.ι (levelDiagram E f k) i
    (((Functor.ofSequence f).map (homOfLE (Nat.zero_le i))).map k ((E 0).point k)) = _ at h
  have hp := ((Functor.ofSequence f).map (homOfLE (Nat.zero_le i))).map_point k
  exact (congrArg (colimit.ι (levelDiagram E f k) i) hp).symm.trans h

/-- Original structure maps followed by the actual next-level colimit inclusions. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:58"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def structureCocone (k : ℕ) : Cocone (levelDiagram E f k) where
  pt := TopCat.of (Path (point E f (k + 1)) (point E f (k + 1)))
  ι :=
    { app := fun i ↦ TopCat.ofHom
        ((basedLoopMap (colimit.ι (levelDiagram E f (k + 1)) i).hom
          (inclusion_point E f (k + 1) i)).comp ((E i).structureMap k))
      naturality := fun i j h ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        apply Path.ext
        funext t
        change colimit.ι (levelDiagram E f (k + 1)) j
            ((E j).structureMap k (((Functor.ofSequence f).map h).map k x) t) =
          colimit.ι (levelDiagram E f (k + 1)) i ((E i).structureMap k x t)
        calc
          _ = colimit.ι (levelDiagram E f (k + 1)) j
              (((Functor.ofSequence f).map h).map (k + 1) ((E i).structureMap k x t)) :=
            congrArg (colimit.ι (levelDiagram E f (k + 1)) j)
              (congrArg (fun p ↦ p t) (((Functor.ofSequence f).map h).comm k x)).symm
          _ = _ := ConcreteCategory.congr_hom (colimit.w (levelDiagram E f (k + 1)) h) _ }

/-- The descended original structure map, using the genuine TopCat universal property. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:80"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def structureMap (k : ℕ) :
    C(levelSpace E f k, Path (point E f (k + 1)) (point E f (k + 1))) :=
  (colimit.desc (levelDiagram E f k) (structureCocone E f k)).hom

/-- The descended structure retains every original stage structure loop. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:85"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem structureMap_inclusion (k i : ℕ) (x : (E i).space k) (t : unitInterval) :
    structureMap E f k (colimit.ι (levelDiagram E f k) i x) t =
      colimit.ι (levelDiagram E f (k + 1)) i ((E i).structureMap k x t) := by
  have h := ConcreteCategory.congr_hom (colimit.ι_desc (structureCocone E f k) i) x
  change structureMap E f k (colimit.ι (levelDiagram E f k) i x) =
    basedLoopMap (colimit.ι (levelDiagram E f (k + 1)) i).hom
      (inclusion_point E f (k + 1) i) ((E i).structureMap k x) at h
  exact congrArg (fun p : Path (point E f (k + 1)) (point E f (k + 1)) ↦ p t) h

/-- The levelwise ordinary colimit with its actual descended prespectrum structure. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:95"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def prespectrum : LoopPrespectrum.{u} where
  space := levelSpace E f
  point := point E f
  structureMap := structureMap E f
  map_point k := by
    ext t
    change structureMap E f k (colimit.ι (levelDiagram E f k) 0 ((E 0).point k)) t = _
    rw [structureMap_inclusion, (E 0).map_point]
    rfl

/-- The original stage inclusions are actual maps of the ordinary colimit prespectrum. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:106"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def inclusion (i : ℕ) : E i ⟶ prespectrum E f where
  map k := (colimit.ι (levelDiagram E f k) i).hom
  map_point k := inclusion_point E f k i
  comm k x := by
    ext t
    exact (structureMap_inclusion E f k i x t).symm

/-- Every original finite transition commutes strictly with the ordinary colimit inclusions. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:114"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem transition_inclusion {i j : ℕ} (h : i ≤ j) :
    Telescope.transition E f i j h ≫ inclusion E f j = inclusion E f i := by
  apply Hom.ext
  funext k
  ext x
  exact ConcreteCategory.congr_hom (colimit.w (levelDiagram E f k) (homOfLE h)) x

/-- The ordinary colimit inclusions commute with the original successor transitions. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:122"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem successor_inclusion (i : ℕ) : f i ≫ inclusion E f (i + 1) = inclusion E f i := by
  simpa only [Telescope.transition_succ] using transition_inclusion E f (Nat.le_succ i)

/-- The original telescope cylinder is sent constantly to the original colimit inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:126"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def collapse : Telescope.prespectrum E f ⟶ prespectrum E f :=
  Telescope.desc E f (inclusion E f) (fun i ↦
    (Homotopy.refl (inclusion E f i)).cast rfl (successor_inclusion E f i).symm)

/-- The actual collapse retains every original stage inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:131"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion.",
  simp]
theorem inclusion_collapse (i : ℕ) :
    Telescope.inclusion E f i ≫ collapse E f = inclusion E f i :=
  Telescope.inclusion_desc _ _ _ _ i

/-- Every point of an original telescope cylinder has its prescribed constant image. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:136"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem collapse_cylinder (k i : ℕ) (s : unitInterval) (x : (E i).space k) :
    (collapse E f).map k (Telescope.cylinder E f k i (s, x)) = (inclusion E f i).map k x := rfl

/-- The original ordinary colimit inclusions form their actual prespectrum cocone. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:140"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def cocone : Cocone (Functor.ofSequence f) where
  pt := prespectrum E f
  ι :=
    { app := inclusion E f
      naturality := fun i j h ↦ by
        change Telescope.transition E f i j (leOfHom h) ≫ inclusion E f j =
          inclusion E f i ≫ 𝟙 _
        rw [Category.comp_id]
        exact transition_inclusion E f (leOfHom h) }

/-- An original prespectrum cocone induces its genuine levelwise topological cocone. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:151"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def levelCocone (c : Cocone (Functor.ofSequence f)) (k : ℕ) :
    Cocone (levelDiagram E f k) where
  pt := c.pt.space k
  ι :=
    { app := fun i ↦ TopCat.ofHom ((c.ι.app i).map k)
      naturality := fun i j h ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        exact congrArg (fun m ↦ m.map k x) (c.w h) }

/-- The actual ordinary colimit descent of an original prespectrum cocone. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:162"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def desc (c : Cocone (Functor.ofSequence f)) : prespectrum E f ⟶ c.pt where
  map k := (colimit.desc (levelDiagram E f k) (levelCocone E f c k)).hom
  map_point k :=
    (ConcreteCategory.congr_hom (colimit.ι_desc (levelCocone E f c k) 0) ((E 0).point k)).trans
      ((c.ι.app 0).map_point k)
  comm k q := by
    obtain ⟨i, x, rfl⟩ := TopCat.SequentialColimit.exists_mem_stageRange
      (colimit.isColimit (levelDiagram E f k)) q
    apply Path.ext
    funext t
    change (colimit.desc (levelDiagram E f (k + 1)) (levelCocone E f c (k + 1)))
        (structureMap E f k (colimit.ι (levelDiagram E f k) i x) t) =
      c.pt.structureMap k
        (colimit.desc (levelDiagram E f k) (levelCocone E f c k)
          (colimit.ι (levelDiagram E f k) i x)) t
    rw [structureMap_inclusion]
    have hk := ConcreteCategory.congr_hom (colimit.ι_desc (levelCocone E f c k) i) x
    have hk' := ConcreteCategory.congr_hom (colimit.ι_desc (levelCocone E f c (k + 1)) i)
      ((E i).structureMap k x t)
    exact hk'.trans ((congrArg (fun p ↦ p t) ((c.ι.app i).comm k x)).trans
      (congrArg (fun y ↦ c.pt.structureMap k y t) hk.symm))

/-- The actual ordinary descent agrees with each original stage map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:185"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem inclusion_desc (c : Cocone (Functor.ofSequence f)) (i : ℕ) :
    inclusion E f i ≫ desc E f c = c.ι.app i := by
  apply Hom.ext
  funext k
  ext x
  exact ConcreteCategory.congr_hom (colimit.ι_desc (levelCocone E f c k) i) x

/-- The levelwise construction is genuinely the ordinary colimit in original prespectra. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:193"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
def isColimit : IsColimit (cocone E f) where
  desc := desc E f
  fac := inclusion_desc E f
  uniq c m hm := by
    apply Hom.ext
    funext k
    ext q
    obtain ⟨i, x, rfl⟩ := TopCat.SequentialColimit.exists_mem_stageRange
      (colimit.isColimit (levelDiagram E f k)) q
    exact (congrArg (fun h ↦ h.map k x) (hm i)).trans
      (congrArg (fun h ↦ h.map k x) (inclusion_desc E f c i)).symm

variable (hc : ∀ i k, IsClosedEmbedding ((f i).map k))

include hc in
/-- The actual level diagram has the supplied original closed-embedding successors. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:209"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem levelDiagram_closed (k i : ℕ) :
    IsClosedEmbedding ((levelDiagram E f k).map (homOfLE (Nat.le_succ i))) := by
  change IsClosedEmbedding (((Functor.ofSequence f).map (homOfLE (Nat.le_succ i))).map k)
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact hc i k

include hc in
/-- Ordinary colimit stage maps are injective, by the original closed-embedding topology. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:217"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem inclusion_injective (k i : ℕ) : Function.Injective ((inclusion E f i).map k) :=
  (TopCat.SequentialColimit.stage_isClosedEmbedding
    (colimit.isColimit (levelDiagram E f k)) (levelDiagram_closed E f hc k) i).injective

variable [∀ i k, T1Space ((E i).space k)]

include hc in
/-- Every actual based sphere class in the ordinary colimit comes from an original stage. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:225"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem exists_homotopyGroup_representative (k n : ℕ)
    (a : HomotopyGroup.Pi n ((prespectrum E f).space k) ((prespectrum E f).point k)) :
    ∃ i, ∃ b : HomotopyGroup.Pi n ((E i).space k) ((E i).point k),
      HomotopyGroup.map ((inclusion E f i).map k) ((inclusion E f i).map_point k) b = a := by
  induction a using Quotient.inductionOn with
  | h p =>
    let : ∀ i, T1Space ((levelDiagram E f k).obj i) :=
      fun i ↦ inferInstanceAs (T1Space ((E i).space k))
    obtain ⟨i, g, hg⟩ := TopCat.SequentialColimit.continuousMap_factors
      (colimit.isColimit (levelDiagram E f k)) (levelDiagram_closed E f hc k) p.val
    let q : GenLoop (Fin n) ((E i).space k) ((E i).point k) := ⟨g, by
      intro x hx
      apply inclusion_injective E f hc k i
      exact (hg x).trans ((p.property x hx).trans (inclusion_point E f k i).symm)⟩
    refine ⟨i, Quotient.mk' q, ?_⟩
    apply congrArg Quotient.mk'
    exact GenLoop.ext _ _ hg

include hc in
/-- A whole compact homotopy in the ordinary colimit is already an original later-stage one. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:245"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem exists_eventual_homotopyGroup_eq (k n : ℕ) {i j : ℕ}
    (a : HomotopyGroup.Pi n ((E i).space k) ((E i).point k))
    (b : HomotopyGroup.Pi n ((E j).space k) ((E j).point k))
    (hab : HomotopyGroup.map ((inclusion E f i).map k) ((inclusion E f i).map_point k) a =
      HomotopyGroup.map ((inclusion E f j).map k) ((inclusion E f j).map_point k) b) :
    ∃ N, ∃ hi : i ≤ N, ∃ hj : j ≤ N,
      HomotopyGroup.map ((Telescope.transition E f i N hi).map k)
          ((Telescope.transition E f i N hi).map_point k) a =
        HomotopyGroup.map ((Telescope.transition E f j N hj).map k)
          ((Telescope.transition E f j N hj).map_point k) b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      obtain ⟨H⟩ := Quotient.exact hab
      let : ∀ i, T1Space ((levelDiagram E f k).obj i) :=
        fun i ↦ inferInstanceAs (T1Space ((E i).space k))
      obtain ⟨N, hN, g, hg⟩ := TopCat.SequentialColimit.continuousMap_factors_above
        (colimit.isColimit (levelDiagram E f k)) (levelDiagram_closed E f hc k)
        H.toHomotopy.toContinuousMap (max i j)
      have hi : i ≤ N := (le_max_left i j).trans hN
      have hj : j ≤ N := (le_max_right i j).trans hN
      have wi (x : (E i).space k) : (inclusion E f N).map k
          ((Telescope.transition E f i N hi).map k x) = (inclusion E f i).map k x :=
        congrArg (fun m ↦ m.map k x) (transition_inclusion E f hi)
      have wj (x : (E j).space k) : (inclusion E f N).map k
          ((Telescope.transition E f j N hj).map k x) = (inclusion E f j).map k x :=
        congrArg (fun m ↦ m.map k x) (transition_inclusion E f hj)
      refine ⟨N, hi, hj, Quotient.sound ⟨?_⟩⟩
      exact {
        toFun := g
        continuous_toFun := g.continuous
        map_zero_left := fun x ↦ inclusion_injective E f hc k N
          ((hg (0, x)).trans ((H.apply_zero x).trans (wi (p x)).symm))
        map_one_left := fun x ↦ inclusion_injective E f hc k N
          ((hg (1, x)).trans ((H.apply_one x).trans (wj (q x)).symm))
        prop' := fun s x hx ↦ inclusion_injective E f hc k N
          ((hg (s, x)).trans ((H.eq_fst s hx).trans (wi (p x)).symm)) }

omit [∀ i k, T1Space ((E i).space k)] in
/-- The actual telescope collapse has exactly the ordinary stage homotopy maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:286"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem collapse_homotopyGroupMap_inclusion (k n i : ℕ)
    (a : HomotopyGroup.Pi n ((E i).space k) ((E i).point k)) :
    HomotopyGroup.map ((collapse E f).map k) ((collapse E f).map_point k)
        (HomotopyGroup.map ((Telescope.inclusion E f i).map k)
          ((Telescope.inclusion E f i).map_point k) a) =
      HomotopyGroup.map ((inclusion E f i).map k) ((inclusion E f i).map_point k) a := by
  induction a using Quotient.inductionOn with
  | h p =>
    apply congrArg Quotient.mk'
    apply GenLoop.ext
    intro z
    exact congrArg (fun m ↦ m.map k (p z)) (inclusion_collapse E f i)

include hc in
/-- The original collapse induces bijections on every based homotopy set, including degree zero. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:301"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem collapse_homotopyGroupMap_bijective (k n : ℕ) :
    Function.Bijective
      (HomotopyGroup.map ((collapse E f).map k) ((collapse E f).map_point k) (N := Fin n)) := by
  constructor
  · intro x y hxy
    obtain ⟨i, a, rfl⟩ := Telescope.exists_homotopyGroup_representative E f k n x
    obtain ⟨j, b, rfl⟩ := Telescope.exists_homotopyGroup_representative E f k n y
    have hab := (collapse_homotopyGroupMap_inclusion E f k n i a).symm.trans
      (hxy.trans (collapse_homotopyGroupMap_inclusion E f k n j b))
    obtain ⟨N, hi, hj, hN⟩ := exists_eventual_homotopyGroup_eq E f hc k n a b hab
    exact (Telescope.inclusion_transition_homotopyGroupMap E f hi k n a).trans
      ((congrArg (HomotopyGroup.map ((Telescope.inclusion E f N).map k)
        ((Telescope.inclusion E f N).map_point k)) hN).trans
          (Telescope.inclusion_transition_homotopyGroupMap E f hj k n b).symm)
  · intro x
    obtain ⟨i, a, ha⟩ := exists_homotopyGroup_representative E f hc k n x
    exact ⟨HomotopyGroup.map ((Telescope.inclusion E f i).map k)
      ((Telescope.inclusion E f i).map_point k) a,
        (collapse_homotopyGroupMap_inclusion E f k n i a).trans ha⟩

include hc in
/-- The actual telescope-to-ordinary-colimit collapse is stable for original closed embeddings. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SequentialColimitStable.lean:323"
  "adaptation" "Original ordinary colimit, literal collapse and closed pushout inclusion."]
theorem collapse_isStableEquivalence : IsStableEquivalence (collapse E f) := by
  intro d
  have hstage (n : ℕ) : IsIso ((stableSystemMap (collapse E f) d).app n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact collapse_homotopyGroupMap_bijective E f hc
      ((-d).toNat + n + 2) (d.toNat + n + 2)
  let : ∀ n, IsIso ((stableSystemMap (collapse E f) d).app n) := hstage
  let : IsIso (stableSystemMap (collapse E f) d) := NatIso.isIso_of_isIso_app _
  change IsIso (colim.map (stableSystemMap (collapse E f) d))
  infer_instance

end Topology.LoopPrespectrum.SequentialColimit

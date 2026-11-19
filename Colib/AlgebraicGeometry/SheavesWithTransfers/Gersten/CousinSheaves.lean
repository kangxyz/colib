/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.SectionsOverAQuasiCompactOpen
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.AbelianSections
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Topology.Sheaves.PUnit

/-! # Direct sums of point sheaves

Over a quasi-compact open, sections of the coproduct of skyscraper sheaves are
exactly the sum of the groups indexed by points of the open. Over a Noetherian
space the resulting sheaf is flasque by extension by zero on these summands.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

universe u v

namespace AlgebraicGeometry.SheafWithTransfers.Gersten

attribute [local instance] Classical.propDecidable

variable (X : TopCat.{u}) {I : Type u} (point : I → X) (A : I → AddCommGrpCat.{v})

/-- The skyscraper sheaf associated with one of the indicated points. -/
def cousinPointSkyscraper (i : I) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v} :=
  ⟨skyscraperPresheaf (point i) (A i), by
    apply (Presheaf.isSheaf_iso_iff
      (eqToIso (skyscraperPresheaf_eq_pushforward (point i) (A i)))).mpr
    apply Sheaf.pushforward_sheaf_of_sheaf
    apply Presheaf.isSheaf_on_punit_of_isTerminal
    dsimp [skyscraperPresheaf]
    have hb : PUnit.unit.{u + 1} ∉ (⊥ : Opens (TopCat.of PUnit.{u + 1})) := fun h ↦ h
    rw [ite_eq_right hb]
    exact terminalIsTerminal⟩

/-- The sections of a point sheaf over an open containing that point. -/
def cousinPointSkyscraperSectionsIso (U : Opens X) (i : I) (hi : point i ∈ U) :
    (cousinPointSkyscraper X point A i).obj.obj (op U) ≅ A i :=
  eqToIso (ite_eq_left hi)

/-- A point sheaf has zero sections on any open missing its point. -/
theorem cousinPointSkyscraperSectionsIsZero (U : Opens X) (i : I) (hi : point i ∉ U) :
    IsZero ((cousinPointSkyscraper X point A i).obj.obj (op U)) :=
  (isZero_zero _).of_iso ((eqToIso (ite_eq_right hi)).trans
    (terminalIsTerminal.uniqueUpToIso (isZero_zero _).isTerminal))

variable [UnivLE.{u, v}]

local instance : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v} := by
  let J := Opens.grothendieckTopology X
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{v, v, u, u} _
  have (U : Opens X) : PreservesColimitsOfShape (J.Cover U)ᵒᵖ
      (CategoryTheory.forget AddCommGrpCat.{v}) := inferInstance
  exact (plusPlusAdjunction J AddCommGrpCat.{v}).isRightAdjoint

local instance (L : Type u) : HasColimitsOfShape (Discrete L)
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}) :=
  CategoryTheory.Sheaf.instHasColimitsOfShape (K := Discrete L)

/-- The sum of the indicated point sheaves. -/
def cousinPointSheaf :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v} :=
  ∐ cousinPointSkyscraper X point A

/-- Include a summand into the sections over an open containing its point. -/
def cousinPointSectionι (U : Opens X) (i : {i : I // point i ∈ U}) :
    A i.1 ⟶ (cousinPointSheaf X point A).obj.obj (op U) :=
  (cousinPointSkyscraperSectionsIso X point A U i.1 i.2).inv ≫
    (Sigma.ι (cousinPointSkyscraper X point A) i.1).hom.app (op U)

/-- Sections over a quasi-compact open are a coproduct of the summands surviving on it. -/
def cousinPointSectionsIsColimit (U : Opens X) (hU : IsCompact (U : Set X)) :
    IsColimit (Cofan.mk _ (cousinPointSectionι X point A U)) := by
  let G := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj (op U)
  let qc := Stacks.Cohomology.Sections.isQuasiCompactObject_of_isCompact U hU
  letI := Stacks.Sites.preservesColimitsOfShape_discrete_sheafSections_of_isQuasiCompactObject
    (Opens.grothendieckTopology X) U qc I
  let h := isColimitOfHasCoproductOfPreservesColimit G (cousinPointSkyscraper X point A)
  let lift (c : Cofan (fun i : {i : I // point i ∈ U} ↦ A i.1)) (j : I) :
      (cousinPointSkyscraper X point A j).obj.obj (op U) ⟶ c.pt :=
    if hj : point j ∈ U then
      (cousinPointSkyscraperSectionsIso X point A U j hj).hom ≫ c.inj ⟨j, hj⟩
    else 0
  refine Cofan.IsColimit.mk _ (fun c ↦ Cofan.IsColimit.desc h (lift c)) ?_ ?_
  · rintro c ⟨j, hj⟩
    change (cousinPointSkyscraperSectionsIso X point A U j hj).inv ≫
      G.map (Sigma.ι (cousinPointSkyscraper X point A) j) ≫ Cofan.IsColimit.desc h (lift c) = _
    have hfac : G.map (Sigma.ι (cousinPointSkyscraper X point A) j) ≫
        Cofan.IsColimit.desc h (lift c) = lift c j := Cofan.IsColimit.fac h (lift c) j
    rw [hfac]
    change _ ≫ (if hj' : point j ∈ U then
      (cousinPointSkyscraperSectionsIso X point A U j hj').hom ≫ c.inj ⟨j, hj'⟩ else 0) = _
    rw [dite_eq_left hj, Iso.inv_hom_id_assoc]
  · intro c m hm
    apply Cofan.IsColimit.hom_ext h
    intro j
    rw [Cofan.IsColimit.fac h (lift c) j]
    by_cases hj : point j ∈ U
    · have h' := hm ⟨j, hj⟩
      change (cousinPointSkyscraperSectionsIso X point A U j hj).inv ≫
        G.map (Sigma.ι (cousinPointSkyscraper X point A) j) ≫ m = c.inj ⟨j, hj⟩ at h'
      change _ = if hj' : point j ∈ U then
        (cousinPointSkyscraperSectionsIso X point A U j hj').hom ≫ c.inj ⟨j, hj'⟩ else 0
      rw [dite_eq_left hj, ← h', Iso.hom_inv_id_assoc]
      rfl
    · exact (cousinPointSkyscraperSectionsIsZero X point A U j hj).eq_of_src _ _

/-- Sections of the point-sum sheaf on a quasi-compact open, with the original injections. -/
def cousinPointSectionsIso (U : Opens X) (hU : IsCompact (U : Set X)) :
    (∐ fun i : {i : I // point i ∈ U} ↦ A i.1) ≅
      (cousinPointSheaf X point A).obj.obj (op U) :=
  IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct _)
    (cousinPointSectionsIsColimit X point A U hU)

@[reassoc (attr := simp)]
theorem cousinPointSectionsIso_ι (U : Opens X) (hU : IsCompact (U : Set X))
    (i : {i : I // point i ∈ U}) :
    Sigma.ι (fun i : {i : I // point i ∈ U} ↦ A i.1) i ≫
      (cousinPointSectionsIso X point A U hU).hom = cousinPointSectionι X point A U i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _)
    (cousinPointSectionsIsColimit X point A U hU) (Discrete.mk i)

/-- A summand surviving on the smaller open restricts by the identity. -/
@[reassoc]
theorem cousinPointSectionι_restrict {U V : Opens X} (f : V ⟶ U)
    (i : I) (hi : point i ∈ V) :
    cousinPointSectionι X point A U ⟨i, f.le hi⟩ ≫
      (cousinPointSheaf X point A).obj.map f.op = cousinPointSectionι X point A V ⟨i, hi⟩ := by
  let e := Sigma.ι (cousinPointSkyscraper X point A) i
  change (cousinPointSkyscraperSectionsIso X point A U i (f.le hi)).inv ≫
    e.hom.app (op U) ≫ (∐ cousinPointSkyscraper X point A).obj.map f.op = _
  rw [← e.hom.naturality]
  change (cousinPointSkyscraperSectionsIso X point A U i (f.le hi)).inv ≫
    (skyscraperPresheaf (point i) (A i)).map f.op ≫ e.hom.app (op V) = _
  simp only [cousinPointSkyscraperSectionsIso, eqToIso, skyscraperPresheaf_map,
    unop_op, dite_eq_left hi, eqToHom_trans_assoc, cousinPointSectionι]
  rfl

/-- A summand whose point is absent from the smaller open restricts to zero. -/
@[reassoc]
theorem cousinPointSectionι_restrict_eq_zero {U V : Opens X} (f : V ⟶ U)
    (i : {i : I // point i ∈ U}) (hi : point i.1 ∉ V) :
    cousinPointSectionι X point A U i ≫ (cousinPointSheaf X point A).obj.map f.op = 0 := by
  let e := Sigma.ι (cousinPointSkyscraper X point A) i.1
  change (cousinPointSkyscraperSectionsIso X point A U i.1 i.2).inv ≫
    e.hom.app (op U) ≫ (∐ cousinPointSkyscraper X point A).obj.map f.op = _
  rw [← e.hom.naturality]
  rw [(cousinPointSkyscraperSectionsIsZero X point A V i.1 hi).eq_of_tgt
    ((cousinPointSkyscraper X point A i.1).obj.map f.op) 0]
  simp

/-- Extension by zero sends every summand of an open to the same summand of the larger open. -/
def cousinPointSectionsExtend {U V : Opens X} (f : V ⟶ U) (hV : IsCompact (V : Set X)) :
    (cousinPointSheaf X point A).obj.obj (op V) ⟶ (cousinPointSheaf X point A).obj.obj (op U) :=
  Cofan.IsColimit.desc (cousinPointSectionsIsColimit X point A V hV)
    (fun i ↦ cousinPointSectionι X point A U ⟨i.1, f.le i.2⟩)

/-- Extension by zero is a section of restriction on every quasi-compact smaller open. -/
@[reassoc (attr := simp)]
theorem cousinPointSectionsExtend_restrict {U V : Opens X} (f : V ⟶ U)
    (hV : IsCompact (V : Set X)) :
    cousinPointSectionsExtend X point A f hV ≫ (cousinPointSheaf X point A).obj.map f.op =
      𝟙 _ := by
  apply Cofan.IsColimit.hom_ext (cousinPointSectionsIsColimit X point A V hV)
  intro i
  have hfac : cousinPointSectionι X point A V i ≫
      cousinPointSectionsExtend X point A f hV =
      cousinPointSectionι X point A U ⟨i.1, f.le i.2⟩ :=
    Cofan.IsColimit.fac (cousinPointSectionsIsColimit X point A V hV)
      (fun j ↦ cousinPointSectionι X point A U ⟨j.1, f.le j.2⟩) i
  change cousinPointSectionι X point A V i ≫ (cousinPointSectionsExtend X point A f hV ≫ _) =
    cousinPointSectionι X point A V i ≫ 𝟙 _
  rw [← Category.assoc, hfac, Category.comp_id]
  exact cousinPointSectionι_restrict X point A f i.1 i.2

/-- Point-sum sheaves on a Noetherian space are flasque. -/
instance [NoetherianSpace X] :
    TopCat.Presheaf.IsFlasque (X := X) (cousinPointSheaf X point A).obj where
  epi {U V} f := by
    let hV := NoetherianSpace.isCompact (V.unop : Set X)
    let s := cousinPointSectionsExtend X point A f.unop hV
    exact (SplitEpi.mk s (cousinPointSectionsExtend_restrict X point A f.unop hV)).epi

end AlgebraicGeometry.SheafWithTransfers.Gersten

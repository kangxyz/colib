/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.AbelianSections
import Colib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteSubfamily
import Colib.AlgebraicGeometry.Sites.Smooth.Noetherian

/-!
# Direct sums on the smooth Nisnevich site

A covering sieve of a smooth scheme over a noetherian base contains a
finite Nisnevich family. Thus sections of abelian sheaves over that
scheme preserve direct sums.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [IsNoetherian S]

/-- Every smooth object over a noetherian base is quasi-compact for the
actual smooth Nisnevich topology. -/
theorem nisnevich_isQuasiCompactObject (X : SmoothSite S) :
    (nisnevichTopology S).IsQuasiCompactObject X := by
  classical
  intro U hU
  obtain ⟨R, hR, hle⟩ := mem_nisnevichTopology_iff.mp hU
  obtain ⟨I, Y, f, rfl⟩ := R.exists_eq_ofArrows
  have hf := (ofArrows_mem_nisnevichPrecoverage_iff f).1 hR
  have hf' : Presieve.ofArrows (fun i => (Y i).left) (fun i => (f i).left) ∈
      Nisnevich.precoverage X.left := (Nisnevich.ofArrows_mem_precoverage_iff _).2 hf
  obtain ⟨s, hs⟩ := Nisnevich.exists_finset_of_mem_precoverage (fun i => (f i).left) hf'
  let V : PreZeroHypercover.{u + 1} X :=
    { I₀ := ULift.{u + 1} s
      X := fun i => Y i.down.val
      f := fun i => f i.down.val }
  have hV : V.presieve₀ ∈ nisnevichPrecoverage S X := by
    apply (ofArrows_mem_nisnevichPrecoverage_iff V.f).2
    refine ⟨fun i => hf.1 i.down.val, fun x => ?_⟩
    obtain ⟨i, hi, y, hxy, he⟩ := hs x
    exact ⟨⟨⟨i, hi⟩⟩, y, hxy, he⟩
  have hcov : V.sieve₀ ∈ nisnevichTopology S X :=
    mem_nisnevichTopology_iff.2 ⟨V.presieve₀, hV, Sieve.le_generate V.presieve₀⟩
  choose a g hg using fun i : V.I₀ =>
    (Sieve.mem_ofArrows_iff _ _ _).1 (hle _ _ (Presieve.ofArrows.mk i.down.val))
  let φ : V.Hom U := ⟨a, g, fun i => (hg i).symm⟩
  let : Finite V.I₀ := inferInstanceAs (Finite (ULift.{u + 1} s))
  exact ⟨V, φ, hcov, Set.finite_range _⟩

/-- Sections of ordinary abelian Nisnevich sheaves over a smooth scheme
preserve direct sums on the original scheme. -/
theorem nisnevichSheafSections_preservesCoproducts (X : SmoothSite S) (I : Type w) :
    PreservesColimitsOfShape (Discrete I)
      ((sheafSections (nisnevichTopology S) AddCommGrpCat.{v}).obj (op X)) :=
  Stacks.Sites.preservesColimitsOfShape_discrete_sheafSections_of_isQuasiCompactObject
    _ X (nisnevich_isQuasiCompactObject X) I

end AlgebraicGeometry.Scheme.SmoothSite

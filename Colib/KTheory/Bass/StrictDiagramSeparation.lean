/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.StrictDiagram
public import Colib.Topology.Prespectrum.StrictSquareSeparation

/-!
# T1 separation of every actual finite strict Bass iterate

Only the initial diagram needs levelwise T1 separation. Induction generalized over that
whole diagram propagates it through the original strict square, cone and parameter loop.
The supplied seed, coefficient row and its geometric construction remain separate data.

Implementation provenance: T1 clauses of `Quillen/KTheory/Bass/StrictDiagramTopology.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- Every original Bass value retains T1 separation at each level. -/
instance strictDiagramFunctorSpaceT1Space (F : C ⥤ LoopPrespectrum.{w})
    [∀ X k, T1Space ((F.obj X).space k)] (X : C) (k : ℕ) :
    T1Space ((((strictDiagramFunctor Q).obj F).obj X).space k) :=
  @LoopPrespectrum.StrictSquare.loopedConeSpaceT1Space
    (F.mapArrow.mapArrow.obj (Q.obj X)) k
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).left.left).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).left.right).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).right.left).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).right.right).space k)))

/-- No new separation premise is needed at later stages of the same original iteration. -/
instance strictDiagramIterateSpaceT1Space (n : ℕ) (F : C ⥤ LoopPrespectrum.{w})
    [∀ X k, T1Space ((F.obj X).space k)] (X : C) (k : ℕ) :
    T1Space ((((strictDiagramIterate Q n).obj F).obj X).space k) := by
  induction n generalizing F with
  | zero => exact inferInstanceAs (T1Space ((F.obj X).space k))
  | succ n ih => exact ih ((strictDiagramFunctor Q).obj F)

end KTheory.Bass

attribute [colib_tag "COL-0354",
  colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramTopology.lean:26-34,54-59" "adaptation"
    "T1 separation of actual finite strict Bass iterates, without point HEP"]
  KTheory.Bass.strictDiagramFunctorSpaceT1Space
  KTheory.Bass.strictDiagramIterateSpaceT1Space

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.StrictDiagramSeparation
public import Colib.Topology.Prespectrum.StrictSquarePointHEP

/-!
# Point HEP under every actual strict Bass iterate

Genuine chosen-point HEP propagates through the existing Bass endofunctor and every
iterate, using the existing native T1 instances. The induction ranges over strict diagrams
and uses the original four corners, double-cylinder point, cone point and loop point.
-/
/-! Implementation provenance: `Quillen/KTheory/Bass/StrictDiagramTopology.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- The original chosen points remain well-based through the literal Bass construction. -/
theorem strictDiagramFunctor_point_homotopyExtensionProperty (F : C ⥤ LoopPrespectrum.{w})
    [∀ X k, T1Space ((F.obj X).space k)]
    (h : ∀ X k, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point k))))
    (X : C) (k : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((((strictDiagramFunctor Q).obj F).obj X).point k))) :=
  @LoopPrespectrum.StrictSquare.loopedCone_point_homotopyExtensionProperty
    (F.mapArrow.mapArrow.obj (Q.obj X)) k
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).left.left).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).left.right).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).right.left).space k)))
    (inferInstanceAs (T1Space ((F.obj (Q.obj X).right.right).space k)))
    (h (Q.obj X).left.left k) (h (Q.obj X).left.right k)
    (h (Q.obj X).right.left k) (h (Q.obj X).right.right k)

/-- Every iterated point has genuine HEP, proved from the initial diagram's original points. -/
theorem strictDiagramIterate_point_homotopyExtensionProperty (n : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) [∀ X k, T1Space ((F.obj X).space k)]
    (h : ∀ X k, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point k))))
    (X : C) (k : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((((strictDiagramIterate Q n).obj F).obj X).point k))) := by
  induction n generalizing F with
  | zero => exact h X k
  | succ n ih =>
    exact ih ((strictDiagramFunctor Q).obj F)
      (strictDiagramFunctor_point_homotopyExtensionProperty Q F h)

end KTheory.Bass

attribute [colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramTopology.lean:37"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  KTheory.Bass.strictDiagramFunctor_point_homotopyExtensionProperty

attribute [colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramTopology.lean:62"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  KTheory.Bass.strictDiagramIterate_point_homotopyExtensionProperty

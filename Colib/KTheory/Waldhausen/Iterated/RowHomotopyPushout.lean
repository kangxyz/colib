/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Waldhausen.Iterated.RowLoopFunctor
public import Colib.Topology.Prespectrum.RowInterchangeHomotopyPushout

/-!
# Genuine row interchange on an original homotopy pushout

The last two actual Waldhausen rows act on each of the three original homotopy-pushout
cells. The overlap height is unchanged. This gives a based involution and the complete
two-structure identity at positive levels. It is a levelwise construction, not a claim
that the transpose itself is a prespectrum endomorphism.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace CategoryTheory.Waldhausen.IteratedS.RowHomotopyPushout
open Topology.LoopPrespectrum
variable {A B C : WideSubcategory preservesZero.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- The unchanged original homotopy-pushout prespectrum of the two exact model maps. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowHomotopyPushout.lean:31"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
abbrev spectrum := HomotopyPushout.prespectrum (prespectrumMap f) (prespectrumMap g)

/-- The original realized transpose, typed at its actual prespectrum level. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowHomotopyPushout.lean:34"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
def vertex (k : ℕ) (W : WideSubcategory preservesZero.{u}) :
    C((prespectrum W).space (k + 3), (prespectrum W).space (k + 3)) :=
  ⟨stageRowSwapHomeomorph k W, (stageRowSwapHomeomorph k W).continuous⟩

/-- The original vertex transpose fixes the specified point. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowHomotopyPushout.lean:39"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem vertex_point (k : ℕ) (W : WideSubcategory preservesZero.{u}) :
    vertex k W ((prespectrum W).point (k + 3)) = (prespectrum W).point (k + 3) :=
  stageRowSwapHomeomorph_point k W

/-- Exact model maps commute with the typed vertex transpose. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowHomotopyPushout.lean:44"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem vertex_naturality (k : ℕ) {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
    (x : (prespectrum V).space (k + 3)) :
    vertex k W ((prespectrumMap F).map (k + 3) x) =
      (prespectrumMap F).map (k + 3) (vertex k V x) :=
  stageRowSwapHomeomorph_naturality k F x

/-- The two original rows transpose on every vertex and on the whole overlap cylinder. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowHomotopyPushout.lean:51"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
def rowSwap (k : ℕ) : C((spectrum f g).space (k + 3), (spectrum f g).space (k + 3)) :=
  RowInterchange.pushout (prespectrumMap f) (prespectrumMap g)
    (fun k => vertex k A) (fun k => vertex k B) (fun k => vertex k C)
    (fun k => vertex_point k A) (fun k => vertex_point k B)
    (fun k x => vertex_naturality k f x) (fun k x => vertex_naturality k g x) k

/-- The left original target is acted on by its actual row transpose. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowHomotopyPushout.lean:84"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem rowSwap_left (k : ℕ) (x : (prespectrum B).space (k + 3)) :
    rowSwap f g k (HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3) x) =
      HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3) (vertex k B x) := rfl

/-- The right original target is acted on by its actual row transpose. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowHomotopyPushout.lean:89"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem rowSwap_right (k : ℕ) (x : (prespectrum C).space (k + 3)) :
    rowSwap f g k (HomotopyPushout.right (prespectrumMap f) (prespectrumMap g) (k + 3) x) =
      HomotopyPushout.right (prespectrumMap f) (prespectrumMap g) (k + 3) (vertex k C x) := rfl

/-- The entire overlap retains its original height. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowHomotopyPushout.lean:94"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem rowSwap_cylinder (k : ℕ) (h : unitInterval)
    (x : (prespectrum A).space (k + 3)) :
    rowSwap f g k (HomotopyPushout.cylinder (prespectrumMap f) (prespectrumMap g) (k + 3) (h, x)) =
      HomotopyPushout.cylinder (prespectrumMap f) (prespectrumMap g) (k + 3)
        (h, vertex k A x) := rfl

/-- The actual pushout basepoint is fixed. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowHomotopyPushout.lean:101"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem rowSwap_point (k : ℕ) :
    rowSwap f g k ((spectrum f g).point (k + 3)) = (spectrum f g).point (k + 3) := by
  exact congrArg (HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3))
    (vertex_point k B)

private theorem vertex_involutive (k : ℕ) (W : WideSubcategory preservesZero.{u})
    (x : (prespectrum W).space (k + 3)) :
    vertex k W (vertex k W x) = x :=
  (stageRowSwapHomeomorph k W).symm_apply_apply x

/-- Applying the genuine quotient row transpose twice is literally the identity. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowHomotopyPushout.lean:112"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem rowSwap_involutive (k : ℕ) : Function.Involutive (rowSwap f g k) := by
  intro q
  induction q using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl x =>
        exact congrArg (HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3))
          (vertex_involutive k B x)
      | inr x =>
        exact congrArg (HomotopyPushout.right (prespectrumMap f) (prespectrumMap g) (k + 3))
          (vertex_involutive k C x)
    | inr z =>
      exact congrArg (fun y =>
        HomotopyPushout.cylinder (prespectrumMap f) (prespectrumMap g) (k + 3) (z.1, y))
        (vertex_involutive k A z.2)

/-- The original two structure times interchange, while the overlap height stays fixed. -/
@[colib_tag "COL-0529", colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowHomotopyPushout.lean:129"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem structure_rowSwap (k : ℕ) (x : (spectrum f g).space (k + 1))
    (s t : unitInterval) :
    rowSwap f g k ((spectrum f g).structureMap (k + 2)
      ((spectrum f g).structureMap (k + 1) x s) t) =
        (spectrum f g).structureMap (k + 2)
          ((spectrum f g).structureMap (k + 1) x t) s := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl x =>
        exact congrArg (HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3))
          (stageLoopMap_rowSwap k B x s t)
      | inr x =>
        exact congrArg (HomotopyPushout.right (prespectrumMap f) (prespectrumMap g) (k + 3))
          (stageLoopMap_rowSwap k C x s t)
    | inr z =>
      exact congrArg (fun y =>
        HomotopyPushout.cylinder (prespectrumMap f) (prespectrumMap g) (k + 3) (z.1, y))
        (stageLoopMap_rowSwap k A z.2 s t)

end CategoryTheory.Waldhausen.IteratedS.RowHomotopyPushout

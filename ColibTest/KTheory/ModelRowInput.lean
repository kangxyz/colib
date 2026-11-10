/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.NaturalModelUnitTrack
public import Colib.KTheory.Bass.ModelDiagramRowInterchange

/-! Actual unit tracks and finite row inputs on native zero-preserving exact objects. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Functor.IdentityAutomorphism
open scoped unitInterval
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (L : C ⥤ C) (c : 𝟭 C ⟶ L)
  (F : C ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)).obj.Obj ≅ 𝟭 (F.obj (L.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y) S,
    (F.map (L.map g)).hom.toFunctor.map ((unit X).hom.app S) =
      (unit Y).hom.app ((F.map (L.map g)).hom.toFunctor.obj S))

example (X : C) : (NaturalTrack.ofModelUnits L c F unit hunit).homotopy X =
    prespectrumIsoHomotopy (F.map (c.app X))
      (onFunctor (F.map (c.app X)).hom.toFunctor (unit X)) := rfl

example {X Y : C} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : (prespectrum (F.obj X)).space n) :
    (prespectrumMap (F.map (L.map g))).map n
      (((NaturalTrack.ofModelUnits L c F unit hunit).homotopy X).level n (r, x)) =
      ((NaturalTrack.ofModelUnits L c F unit hunit).homotopy Y).level n
        (r, (prespectrumMap (F.map g)).map n x) :=
  (NaturalTrack.ofModelUnits L c F unit hunit).naturality g n r x

variable (Q : C ⥤ Arrow (Arrow C))
open ModelDiagramRowInterchange

example (i : ℕ) (X : C) (k : ℕ) :
    stage Q F i X k ((((strictDiagramIterate Q i).obj
      (F ⋙ prespectrumFunctor)).obj X).point (k + 3)) =
        (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).point (k + 3) :=
  stage_point Q F i X k

example (i : ℕ) {X Y : C} (g : X ⟶ Y) (k : ℕ)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space (k + 3)) :
    stage Q F i Y k
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).map g).map (k + 3) x) =
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).map g).map (k + 3)
        (stage Q F i X k x) := by
  exact stage_naturality Q F i g k x

example (i : ℕ) (X : C) (k : ℕ)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space (k + 1))
    (s t : unitInterval) :
    stage Q F i X k
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).structureMap (k + 2)
        ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).structureMap
          (k + 1) x s) t) =
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).structureMap (k + 2)
        ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).structureMap
          (k + 1) x t) s :=
  stage_structure Q F i X k x s t

example (i : ℕ) (X : C) (k : ℕ) :
    cone Q i F X k
      (((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj
        (F ⋙ prespectrumFunctor))).obj X).point (k + 3)) =
      ((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj
        (F ⋙ prespectrumFunctor))).obj X).point (k + 3) :=
  cone_point Q i F X k

section
variable {A B D : WideSubcategory preservesZero.{w}} (f : A ⟶ B) (g : A ⟶ D)
open CategoryTheory.Waldhausen.IteratedS.RowHomotopyPushout

example (k : ℕ) (x : (prespectrum B).space (k + 3)) :
    rowSwap f g k (HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3) x) =
      HomotopyPushout.left (prespectrumMap f) (prespectrumMap g) (k + 3) (vertex k B x) :=
  rowSwap_left f g k x

example (k : ℕ) : Function.Involutive (rowSwap f g k) :=
  rowSwap_involutive f g k
end

end KTheory.Bass

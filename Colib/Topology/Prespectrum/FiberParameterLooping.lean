/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Loop
public import Colib.Topology.Prespectrum.FiberNaturality
public import Colib.Topology.Prespectrum.ParameterLooping

/-!
# Actual fibers commute with parameter-correct looping

Transposing the independent loop and fiber-path parameters gives an isomorphism of the original
prespectra. Both directions retain the source coordinate and the full fiber path. The isomorphism
commutes strictly with the actual fiber projections and is natural in strict arrow squares.
No separation, homotopy extension, or Omega hypothesis is needed.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiberParameterLooping.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual fiber-loop transpose retains both source coordinates and complete
fiber paths, independent parameters, projections and strict-square naturality. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- Literal transposition identifies the fiber of parameter looping with parameter looping of the
actual fiber, including their original structure maps. -/
def homotopyFiberParameterLoopingIso :
    homotopyFiber (parameterLoopingMap f) ≅ parameterLooping (homotopyFiber f) where
  hom :=
    { map n := (HomotopyFiber.loopFiberHomeomorph (f.map n) (f.map_point n)).toHomotopyEquiv.toFun
      map_point n := HomotopyFiber.loopFiberHomeomorph_basepoint (f.map n) (f.map_point n)
      comm n z := by
        apply Path.ext
        funext t
        apply Path.ext
        funext s
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply ContinuousMap.ext
          intro r
          rfl }
  inv :=
    { map n := (HomotopyFiber.loopFiberHomeomorph (f.map n)
        (f.map_point n)).symm.toHomotopyEquiv.toFun
      map_point n := by
        apply Subtype.ext
        apply Prod.ext
        · apply Path.ext
          funext t
          rfl
        · apply ContinuousMap.ext
          intro s
          apply Path.ext
          funext t
          rfl
      comm n γ := by
        apply Path.ext
        funext t
        apply Subtype.ext
        apply Prod.ext
        · apply Path.ext
          funext s
          rfl
        · apply ContinuousMap.ext
          intro r
          apply Path.ext
          funext s
          rfl }
  hom_inv_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    exact (HomotopyFiber.loopFiberHomeomorph (f.map n) (f.map_point n)).left_inv z
  inv_hom_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro γ
    exact (HomotopyFiber.loopFiberHomeomorph (f.map n) (f.map_point n)).right_inv γ

@[simp] theorem homotopyFiberParameterLoopingIso_hom_source (n : ℕ)
    (z : (homotopyFiber (parameterLoopingMap f)).space n) (t : unitInterval) :
    (Path.toContinuousMap ((homotopyFiberParameterLoopingIso f).hom.map n z) t).1.1 =
      Path.toContinuousMap z.1.1 t := rfl

@[simp] theorem homotopyFiberParameterLoopingIso_hom_path (n : ℕ)
    (z : (homotopyFiber (parameterLoopingMap f)).space n) (t s : unitInterval) :
    (Path.toContinuousMap ((homotopyFiberParameterLoopingIso f).hom.map n z) t).1.2 s =
      Path.toContinuousMap (z.1.2 s) t := rfl

@[simp] theorem homotopyFiberParameterLoopingIso_inv_source (n : ℕ)
    (γ : (parameterLooping (homotopyFiber f)).space n) (t : unitInterval) :
    Path.toContinuousMap ((homotopyFiberParameterLoopingIso f).inv.map n γ).1.1 t =
      (Path.toContinuousMap γ t).1.1 := rfl

@[simp] theorem homotopyFiberParameterLoopingIso_inv_path (n : ℕ)
    (γ : (parameterLooping (homotopyFiber f)).space n) (s t : unitInterval) :
    Path.toContinuousMap (((homotopyFiberParameterLoopingIso f).inv.map n γ).1.2 s) t =
      (Path.toContinuousMap γ t).1.2 s := rfl

/-- The forward transpose preserves the entire actual source loop. -/
@[simp] theorem homotopyFiberParameterLoopingIso_hom_projection :
    (homotopyFiberParameterLoopingIso f).hom ≫
        parameterLoopingMap (homotopyFiberProjection f) =
      homotopyFiberProjection (parameterLoopingMap f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext t
  rfl

/-- The reverse transpose preserves the entire actual source loop. -/
@[simp] theorem homotopyFiberParameterLoopingIso_inv_projection :
    (homotopyFiberParameterLoopingIso f).inv ≫
        homotopyFiberProjection (parameterLoopingMap f) =
      parameterLoopingMap (homotopyFiberProjection f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext t
  rfl

variable {A B : Arrow LoopPrespectrum.{u}}

/-- Transposing the actual fiber paths is strictly natural in the original arrow square. -/
theorem homotopyFiberParameterLoopingIso_hom_naturality (sq : A ⟶ B) :
    homotopyFiberMap (parameterLoopingFunctor.mapArrow.map sq) ≫
        (homotopyFiberParameterLoopingIso B.hom).hom =
      (homotopyFiberParameterLoopingIso A.hom).hom ≫
        parameterLoopingMap (homotopyFiberMap sq) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext t
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro s
    rfl

/-- The reverse transpose is strictly natural in the same original arrow square. -/
theorem homotopyFiberParameterLoopingIso_inv_naturality (sq : A ⟶ B) :
    parameterLoopingMap (homotopyFiberMap sq) ≫
        (homotopyFiberParameterLoopingIso B.hom).inv =
      (homotopyFiberParameterLoopingIso A.hom).inv ≫
        homotopyFiberMap (parameterLoopingFunctor.mapArrow.map sq) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Subtype.ext
  apply Prod.ext
  · apply Path.ext
    funext t
    rfl
  · apply ContinuousMap.ext
    intro s
    apply Path.ext
    funext t
    rfl

/-- The fiber-loop transpose is a natural isomorphism before any localization. -/
def homotopyFiberParameterLoopingNatIso :
    parameterLoopingFunctor.mapArrow ⋙ homotopyFiberFunctor ≅
      homotopyFiberFunctor ⋙ parameterLoopingFunctor :=
  NatIso.ofComponents (fun A ↦ homotopyFiberParameterLoopingIso A.hom)
    (fun {_ _} sq ↦ homotopyFiberParameterLoopingIso_hom_naturality sq)

end Topology.LoopPrespectrum

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.EndpointHomotopy

/-! # Actual homotopy descent and the self-double-cylinder fold -/
/-! Adapted from `Quillen/Topology/DoubleMappingCylinder/HomotopyDescent.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval
universe u
namespace TopCat.DoubleCylinder
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable {Y : Type u} [TopologicalSpace Y]

/-- A supplied actual homotopy defines the original cylinder map with time last. -/
def homotopyCylinderMap (h₀ : C(B, Y)) (h₁ : C(C, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp g.hom)) : A ⊗ TopCat.I ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨fun z ↦ H (z.2.down, z.1), H.continuous.comp (by fun_prop)⟩

/-- The original two maps define the map on the actual endpoint coproduct. -/
def homotopyEndMap (h₀ : C(B, Y)) (h₁ : C(C, Y)) : TopCat.of (B ⊕ C) ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨Sum.elim h₀ h₁, continuous_sum_dom.mpr ⟨h₀.continuous, h₁.continuous⟩⟩

/-- The supplied homotopy's actual endpoint equations give the exact descent square. -/
theorem homotopyDescent_square (h₀ : C(B, Y)) (h₁ : C(C, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp g.hom)) :
    TopCat.intervalEndpoints A ≫ homotopyCylinderMap f g h₀ h₁ H =
      endMap f g ≫ homotopyEndMap h₀ h₁ := by
  ext a
  cases a with
  | inl a => exact H.map_zero_left a
  | inr a => exact H.map_one_left a

/-- The original pushout descends a genuine homotopy between endpoint composites. -/
def homotopyDesc (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (h₀ : C(B, Y)) (h₁ : C(C, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp g.hom)) : C(D, Y) :=
  (sq.desc (homotopyCylinderMap f g h₀ h₁ H) (homotopyEndMap h₀ h₁)
    (homotopyDescent_square f g h₀ h₁ H)).hom

/-- Descent recovers the unchanged left endpoint map. -/
@[simp] theorem homotopyDesc_left
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (h₀ : C(B, Y)) (h₁ : C(C, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp g.hom)) :
    (homotopyDesc f g sq h₀ h₁ H).comp (gapLeftEndpoint e) = h₀ := by
  ext b
  exact ConcreteCategory.congr_hom (sq.inr_desc (homotopyCylinderMap f g h₀ h₁ H)
    (homotopyEndMap h₀ h₁) (homotopyDescent_square f g h₀ h₁ H)) (Sum.inl b)

/-- Descent recovers the unchanged right endpoint map. -/
@[simp] theorem homotopyDesc_right
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (h₀ : C(B, Y)) (h₁ : C(C, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp g.hom)) :
    (homotopyDesc f g sq h₀ h₁ H).comp (gapRightEndpoint e) = h₁ := by
  ext c
  exact ConcreteCategory.congr_hom (sq.inr_desc (homotopyCylinderMap f g h₀ h₁ H)
    (homotopyEndMap h₀ h₁) (homotopyDescent_square f g h₀ h₁ H)) (Sum.inr c)

/-- Descent retains the entire supplied track on the original cylinder. -/
@[simp] theorem homotopyDesc_apply_cylinder
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (h₀ : C(B, Y)) (h₁ : C(C, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp g.hom)) (t : unitInterval) (a : A) :
    homotopyDesc f g sq h₀ h₁ H (l (a, ULift.up t)) = H (t, a) :=
  ConcreteCategory.congr_hom (sq.inl_desc (homotopyCylinderMap f g h₀ h₁ H)
    (homotopyEndMap h₀ h₁) (homotopyDescent_square f g h₀ h₁ H)) (a, ULift.up t)

/-- The self-cylinder fold is the actual descent of the constant homotopy of f. -/
def selfFold {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ B) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f f) l e) : C(D, B) :=
  homotopyDesc f f sq (ContinuousMap.id B) (ContinuousMap.id B)
    (ContinuousMap.Homotopy.refl f.hom)

/-- The self-fold composed with the unchanged left end is literally identity. -/
@[simp] theorem selfFold_left {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ B) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f f) l e) :
    (selfFold f sq).comp (gapLeftEndpoint e) = ContinuousMap.id B :=
  homotopyDesc_left f f sq _ _ _

/-- The self-fold composed with the unchanged right end is literally identity. -/
@[simp] theorem selfFold_right {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ B) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f f) l e) :
    (selfFold f sq).comp (gapRightEndpoint e) = ContinuousMap.id B :=
  homotopyDesc_right f f sq _ _ _

end TopCat.DoubleCylinder

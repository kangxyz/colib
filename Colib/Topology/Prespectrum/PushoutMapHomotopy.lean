/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.PushoutMovingHomotopy
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# Whole homotopies of the original strict reduced pushout maps

Three specified whole side homotopies, commuting with the original two attaching maps at
every time, induce a homotopy of the unchanged strict pushout maps. The construction uses
the existing moving-boundary quotient descent. Its overlap square retains the original
cylinder coordinate, independently of the homotopy and prespectrum structure parameters.
The endpoint casts only identify the two presentations of the same original quotient map.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C A' B' C' : LoopPrespectrum.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')

/-- The original target overlap track, precomposed by the specified strict source map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutMapHomotopy.lean:32-39"
  "adaptation" "Original whole maps and independent time coordinates retained"]
def strictMapTrack (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (hf : f ≫ b = a ≫ f') (hg : g ≫ c = a ≫ g') :
    Homotopy (f ≫ (b ≫ inl f' g')) (g ≫ (c ≫ inr f' g')) :=
  (Homotopy.precomp a (glue f' g')).cast
    (by rw [← Category.assoc, ← hf, Category.assoc])
    (by rw [← Category.assoc, ← hg, Category.assoc])

/-- This descent is the same original strict quotient map, on all three generators. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutMapHomotopy.lean:40-57"
  "adaptation" "Original whole maps and independent time coordinates retained"]
theorem map_eq_desc_strictMapTrack (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (hf : f ≫ b = a ≫ f') (hg : g ≫ c = a ≫ g') :
    map f g f' g' a b c hf hg =
      desc f g (b ≫ inl f' g') (c ≫ inr f' g') (strictMapTrack f g f' g' a b c hf hg) := by
  apply hom_ext
  · apply Hom.ext; funext n; ext x; rfl
  · apply Hom.ext; funext n; ext x; rfl
  · intro n s x
    rfl

variable {a₀ a₁ : A ⟶ A'} {b₀ b₁ : B ⟶ B'} {c₀ c₁ : C ⟶ C'}
    (hf₀ : f ≫ b₀ = a₀ ≫ f') (hg₀ : g ≫ c₀ = a₀ ≫ g')
    (hf₁ : f ≫ b₁ = a₁ ≫ f') (hg₁ : g ≫ c₁ = a₁ ≫ g')
    (L : Homotopy a₀ a₁) (M : Homotopy b₀ b₁) (N : Homotopy c₀ c₁)
    (hM : ∀ n r x, M.level n (r, f.map n x) = f'.map n (L.level n (r, x)))
    (hN : ∀ n r x, N.level n (r, g.map n x) = g'.map n (L.level n (r, x)))

/-- Move the source point in the original overlap cylinder while keeping its height unchanged. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutMapHomotopy.lean:58-75"
  "adaptation" "Original whole maps and independent time coordinates retained"]
def strictMapMovingSquare :
    (strictMapTrack f g f' g' a₀ b₀ c₀ hf₀ hg₀).Square
      (strictMapTrack f g f' g' a₁ b₁ c₁ hf₁ hg₁)
      (Homotopy.precomp f (M.postcomp (inl f' g')))
      (Homotopy.precomp g (N.postcomp (inr f' g'))) where
  level n := ⟨fun z ↦ cylinder f' g' n (z.2.1, L.level n (z.1, z.2.2)),
    (cylinder f' g' n).continuous.comp (by fun_prop)⟩
  at_zero n s x := congrArg (fun y ↦ cylinder f' g' n (s, y)) (L.at_zero n x)
  at_one n s x := congrArg (fun y ↦ cylinder f' g' n (s, y)) (L.at_one n x)
  left n r x := (cylinder_zero f' g' n _).trans (congrArg (left f' g' n) (hM n r x).symm)
  right n r x := (cylinder_one f' g' n _).trans (congrArg (right f' g' n) (hN n r x).symm)
  at_point n r s := by
    change cylinder f' g' n (s, L.level n (r, A.point n)) = point f' g' n
    rw [L.at_point]
    exact cylinder_point f' g' n s
  comm n r s x t :=
    congrArg (fun y ↦ cylinder f' g' (n + 1) (s, y)) (L.comm n r x t)

/-- The existing moving-boundary descent gives the whole homotopy of the original strict maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutMapHomotopy.lean:76-83"
  "adaptation" "Original whole maps and independent time coordinates retained"]
def mapHomotopy :
    Homotopy (map f g f' g' a₀ b₀ c₀ hf₀ hg₀) (map f g f' g' a₁ b₁ c₁ hf₁ hg₁) :=
  (descSquareHomotopy f g (M.postcomp (inl f' g')) (N.postcomp (inr f' g'))
    (strictMapMovingSquare f g f' g' hf₀ hg₀ hf₁ hg₁ L M N hM hN)).cast
      (map_eq_desc_strictMapTrack f g f' g' a₀ b₀ c₀ hf₀ hg₀).symm
      (map_eq_desc_strictMapTrack f g f' g' a₁ b₁ c₁ hf₁ hg₁).symm

/-- The entire original left face is the moving left side followed by the same inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutMapHomotopy.lean:84-88"
  "adaptation" "Original whole maps and independent time coordinates retained", simp]
theorem mapHomotopy_inl (n : ℕ) (r : unitInterval) (y : B.space n) :
    (mapHomotopy f g f' g' hf₀ hg₀ hf₁ hg₁ L M N hM hN).level n
      (r, (inl f g).map n y) = (inl f' g').map n (M.level n (r, y)) := rfl

/-- The entire original right face is the moving right side followed by the same inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutMapHomotopy.lean:89-93"
  "adaptation" "Original whole maps and independent time coordinates retained", simp]
theorem mapHomotopy_inr (n : ℕ) (r : unitInterval) (y : C.space n) :
    (mapHomotopy f g f' g' hf₀ hg₀ hf₁ hg₁ L M N hM hN).level n
      (r, (inr f g).map n y) = (inr f' g').map n (N.level n (r, y)) := rfl

/-- Every overlap point keeps its cylinder height separate from the actual homotopy time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutMapHomotopy.lean:94-98"
  "adaptation" "Original whole maps and independent time coordinates retained", simp]
theorem mapHomotopy_cylinder (n : ℕ) (r s : unitInterval) (x : A.space n) :
    (mapHomotopy f g f' g' hf₀ hg₀ hf₁ hg₁ L M N hM hN).level n
      (r, cylinder f g n (s, x)) = cylinder f' g' n (s, L.level n (r, x)) := rfl

end Topology.LoopPrespectrum.HomotopyPushout

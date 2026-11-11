/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeHomotopy
public import Colib.Topology.Prespectrum.HomotopyTransport

/-! # Original same-time telescope null from compatible whole stage nulls

Only the original mapNullHomotopy and cylinder formula are selected here.
Cone descent and its cone-isomorphism factorization are not included.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (G : ℕ → LoopPrespectrum.{u}) (h : ∀ i, G i ⟶ G (i + 1))
    (a : ∀ i, E i ⟶ F i) (b : ∀ i, F i ⟶ G i)
    (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))
    (hb : ∀ i, b i ≫ h i = g i ≫ b (i + 1))
    (N : ∀ i, Homotopy (a i ≫ b i) (zeroHom (E i) (G i)))
    (hN : ∀ i k r x, (h i).map k ((N i).level k (r, x)) =
      (N (i + 1)).level k (r, (f i).map k x))

/-- The literal original telescope homotopy, with only its proven composite/zero endpoints cast. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeConeDescent.lean:35"
  "adaptation" "Original whole null, independent times and exact comparison."]
def mapNullHomotopy :
    Homotopy (map E f F g a ha ≫ map F g G h b hb)
      (zeroHom (prespectrum E f) (prespectrum G h)) :=
  (mapHomotopy E f G h (fun i ↦ a i ≫ b i) (fun i ↦ zeroHom (E i) (G i))
    (by intro i; rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc])
    (by
      intro i
      apply Hom.ext
      funext k
      ext x
      exact (h i).map_point k)
    N hN).cast (by apply hom_ext; intros; rfl) (by
      apply hom_ext
      intro k i t x
      exact cylinder_point G h k i t)

/-- The original null time and original telescope height are retained independently. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeConeDescent.lean:52"
  "adaptation" "Original whole null, independent times and exact comparison."]
theorem mapNullHomotopy_cylinder (k i : ℕ) (r t : unitInterval) (x : (E i).space k) :
    (mapNullHomotopy E f F g G h a b ha hb N hN).level k
        (r, cylinder E f k i (t, x)) =
      cylinder G h k i (t, (N i).level k (r, x)) := rfl


end Topology.LoopPrespectrum.Telescope

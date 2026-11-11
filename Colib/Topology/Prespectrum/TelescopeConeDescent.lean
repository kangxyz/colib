/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeConeIso
public import Colib.Topology.Prespectrum.TelescopeMapNullHomotopy
public import Colib.Topology.Prespectrum.ConeDescNaturality

/-!
# Original cone descents and strictly compatible telescope null tracks

The original telescope homotopy of a compatible stage null family descends from the cone of
the unchanged telescope map. This descent factors through the actual telescope-cone isomorphism
and the telescope of the original stage descents. All cylinder and homotopy times are literal;
no point-set separation, excision or stable-equivalence premise is used for this equality.
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

include hb hN in
/-- The prescribed full stage-null square makes the original stage cone descents compatible. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/TelescopeConeDescent.lean:59"
  "adaptation" "Original telescope cone descent, same whole null and signed stable boundary"]
theorem coneDesc_transition (i : ℕ) :
    mappingConeDesc (a i) (b i) (N i) ≫ h i =
      coneTransition E f F g a ha i ≫ mappingConeDesc (a (i + 1)) (b (i + 1)) (N (i + 1)) :=
  (mappingConeDesc_naturality (coneTransitionSquare E f F g a ha i)
    (b i) (b (i + 1)) (h i) (N i) (N (i + 1)) (hb i).symm (hN i)).symm

/-- The unchanged telescope of the original cone descents. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/TelescopeConeDescent.lean:66"
  "adaptation" "Original telescope cone descent, same whole null and signed stable boundary"]
def coneDescMap :
    prespectrum (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) ⟶ prespectrum G h :=
  map (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) G h
    (fun i ↦ mappingConeDesc (a i) (b i) (N i))
    (coneDesc_transition E f F g G h a b ha hb N hN)

/-- The actual telescope-cone isomorphism factors the specified original null descent literally. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/TelescopeConeDescent.lean:73"
  "adaptation" "Original telescope cone descent, same whole null and signed stable boundary"]
theorem coneIso_desc :
    (coneIso E f F g a ha).hom ≫ coneDescMap E f F g G h a b ha hb N hN =
      mappingConeDesc (map E f F g a ha) (map F g G h b hb)
        (mapNullHomotopy E f F g G h a b ha hb N hN) := by
  apply mappingCone_hom_ext
  · apply hom_ext
    intros
    rfl
  · intro k r q
    induction q using Quot.inductionOn with
    | h z => rfl

/-- The original telescope-of-cones cylinder retains its height after descent. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/TelescopeConeDescent.lean:86"
  "adaptation" "Original telescope cone descent, same whole null and signed stable boundary"]
theorem coneDescMap_cylinder (k i : ℕ) (t : unitInterval)
    (q : (mappingCone (a i)).space k) :
    (coneDescMap E f F g G h a b ha hb N hN).map k
        (cylinder (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) k i (t, q)) =
      cylinder G h k i (t, (mappingConeDesc (a i) (b i) (N i)).map k q) := rfl

end Topology.LoopPrespectrum.Telescope

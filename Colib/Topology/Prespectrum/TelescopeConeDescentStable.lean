/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeConeDescent
public import Colib.Topology.Prespectrum.TelescopeStableEquivalence
public import Colib.Topology.Prespectrum.TelescopeConeExcision
public import Colib.Topology.Prespectrum.ConeDescStableEquivalence

/-!
# Stable original telescope cone descent and its signed boundary

The actual point-set factorization and genuine telescope stability transfer stagewise cone
descent stability to the unchanged telescope descent. Only original levelwise T1 separation is
needed for this transfer; no uniform whole-telescope connectivity or point HEP is assumed.
Separately, actual stage cone-fiber excision supplies the original telescope's signed boundary.
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
    [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((F i).space k)]
    [∀ i k, T1Space ((G i).space k)]

/-- Genuine original stage descent stability passes to the same actual telescope cone descent. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/TelescopeConeDescentStable.lean:39"
  "adaptation" "Original telescope cone descent, same whole null and signed stable boundary"]
theorem coneDesc_isStableEquivalence
    (hdesc : ∀ i, IsStableEquivalence (mappingConeDesc (a i) (b i) (N i))) :
    IsStableEquivalence (mappingConeDesc (map E f F g a ha) (map F g G h b hb)
      (mapNullHomotopy E f F g G h a b ha hb N hN)) := by
  rw [← coneIso_desc]
  apply IsStableEquivalence.comp
  · intro d
    infer_instance
  · exact map_isStableEquivalence (fun i ↦ mappingCone (a i))
      (coneTransition E f F g a ha) G h (fun i ↦ mappingConeDesc (a i) (b i) (N i))
      (coneDesc_transition E f F g G h a b ha hb N hN) hdesc

omit [∀ i k, T1Space ((G i).space k)] in
/-- The actual signed boundary uses stage excision and the same complete telescope null lift. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/TelescopeConeDescentStable.lean:53"
  "adaptation" "Original telescope cone descent, same whole null and signed stable boundary"]
theorem coneDesc_connecting
    (he : ∀ i, IsStableEquivalence (mappingConeFiberComparison (a i))) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        (mappingConeDesc (map E f F g a ha) (map F g G h b hb)
          (mapNullHomotopy E f F g G h a b ha hb N hN)) ≫
      stableFiberConnecting (map F g G h b hb) d =
    stableMappingConeConnecting (map E f F g a ha)
      (coneFiberComparison_isStableEquivalence E f F g a ha he) d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift (map F g G h b hb)
          (map E f F g a ha) (mapNullHomotopy E f F g G h a b ha hb N hN)) :=
  mappingConeDesc_connecting _ _ _
    (coneFiberComparison_isStableEquivalence E f F g a ha he) d

end Topology.LoopPrespectrum.Telescope

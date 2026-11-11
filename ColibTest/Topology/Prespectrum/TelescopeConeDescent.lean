module
import Colib.Topology.Prespectrum.TelescopeConeDescentStable

open CategoryTheory Topology Topology.LoopPrespectrum Topology.LoopPrespectrum.Telescope
noncomputable section
universe u

variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (G : ℕ → LoopPrespectrum.{u}) (h : ∀ i, G i ⟶ G (i + 1))
    (a : ∀ i, E i ⟶ F i) (b : ∀ i, F i ⟶ G i)
    (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))
    (hb : ∀ i, b i ≫ h i = g i ≫ b (i + 1))
    (N : ∀ i, Homotopy (a i ≫ b i) (zeroHom (E i) (G i)))
    (hN : ∀ i k r x, (h i).map k ((N i).level k (r, x)) =
      (N (i + 1)).level k (r, (f i).map k x))

example (i : ℕ) :
    mappingConeDesc (a i) (b i) (N i) ≫ h i =
      coneTransition E f F g a ha i ≫ mappingConeDesc (a (i + 1)) (b (i + 1)) (N (i + 1)) :=
  coneDesc_transition E f F g G h a b ha hb N hN i

example :
    (coneIso E f F g a ha).hom ≫ coneDescMap E f F g G h a b ha hb N hN =
      mappingConeDesc (map E f F g a ha) (map F g G h b hb)
        (mapNullHomotopy E f F g G h a b ha hb N hN) :=
  coneIso_desc E f F g G h a b ha hb N hN

example (k i : ℕ) (r t : unitInterval) (x : (E i).space k) :
    (coneDescMap E f F g G h a b ha hb N hN).map k
      (cylinder (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) k i
        (t, ReducedMappingCone.cylinder ((E i).point k) ((F i).point k)
          ((a i).map k) (r, x))) =
      cylinder G h k i (t, (N i).level k (r, x)) := rfl

variable [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((F i).space k)]
    [∀ i k, T1Space ((G i).space k)]

example (hdesc : ∀ i, IsStableEquivalence (mappingConeDesc (a i) (b i) (N i))) :
    IsStableEquivalence (mappingConeDesc (map E f F g a ha) (map F g G h b hb)
      (mapNullHomotopy E f F g G h a b ha hb N hN)) :=
  coneDesc_isStableEquivalence E f F g G h a b ha hb N hN hdesc

example (hdesc : ∀ i, IsStableEquivalence (mappingConeDesc (a i) (b i) (N i))) (j : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat j + 1))).map
      (mappingConeDesc (map E f F g a ha) (map F g G h b hb)
        (mapNullHomotopy E f F g G h a b ha hb N hN))) :=
  coneDesc_isStableEquivalence E f F g G h a b ha hb N hN hdesc _

omit [∀ i k, T1Space ((G i).space k)] in
example (he : ∀ i, IsStableEquivalence (mappingConeFiberComparison (a i))) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        (mappingConeDesc (map E f F g a ha) (map F g G h b hb)
          (mapNullHomotopy E f F g G h a b ha hb N hN)) ≫
      stableFiberConnecting (map F g G h b hb) d =
    stableMappingConeConnecting (map E f F g a ha)
      (coneFiberComparison_isStableEquivalence E f F g a ha he) d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift (map F g G h b hb)
          (map E f F g a ha) (mapNullHomotopy E f F g G h a b ha hb N hN)) :=
  coneDesc_connecting E f F g G h a b ha hb N hN he d

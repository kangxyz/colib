/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionPoints
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MilnorSymbol
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.TupleFieldChange
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# Presentation transport for diagonal corestrictions

An algebra equivalence identifies the actual finite-point maps. The resulting
spectrum isomorphism preserves the original prime cycle and hence the
transferred graph and its diagonal class.

Adapted from `Motivic/Cohomology/Diagonal/CorestrictionPresentationTransport.lean:85-165`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u w

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers
open DiagonalCycleSymbols DiagonalFieldChange DiagonalMilnorSymbol
open DiagonalFiniteCyclePushforward (scalarMap)

variable {k E F : Type u} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]

/-- Both presentations have the same finite-point map after the actual spectrum morphism. -/
theorem finitePointMap_algHom (φ : E →ₐ[k] F) (q : ℕ) (a : Fin q → Eˣ) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ finitePointMap (k := k) q (rationalTuple E q a) =
      finitePointMap (k := k) q
        (rationalTuple F q (fun i => Units.map φ.toRingHom.toMonoidHom (a i))) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, finitePointMap_fst]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext x
    exact φ.commutes x
  · simp only [Category.assoc, finitePointMap_snd]
    exact rationalTuple_algHom φ q a

variable [Module.Finite k E] [Module.Finite k F]

/-- An algebra equivalence preserves the transferred graph with its image multiplicity. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/CorestrictionPresentationTransport.lean:103-120"
  "adaptation" "The actual degree-weighted transferred graphs agree across algebra presentations"]
theorem pointPushforward_graph_algEquiv (ε : E ≃ₐ[k] F) (q : ℕ) (a : Fin q → Eˣ) :
    pointPushforward (k := k) q ((Cor.graphFunctor E).map (rationalTuple E q a)) =
      pointPushforward (k := k) q ((Cor.graphFunctor F).map
        (rationalTuple F q (fun i => Units.map ε.toRingHom.toMonoidHom (a i)))) := by
  let e : Spec (.of F) ≅ Spec (.of E) := Scheme.Spec.mapIso ε.toRingEquiv.toCommRingCatIso.op
  have he : finiteCyclePushforward e.hom (AlgebraicCycle.fundamentalCycle (Spec (.of F))) =
      AlgebraicCycle.fundamentalCycle (Spec (.of E)) :=
    finiteCyclePushforward_fundamentalCycle_iso e
  apply Subtype.ext
  rw [pointPushforward_graph_fundamental, pointPushforward_graph_fundamental,
    ← he,
    finiteCyclePushforward_comp_apply]
  have h (f g : Spec (.of F) ⟶ pointAmbient k q) [IsFinite f] [IsFinite g] (he : f = g) :
      finiteCyclePushforward f (AlgebraicCycle.fundamentalCycle (Spec (.of F))) =
        finiteCyclePushforward g (AlgebraicCycle.fundamentalCycle (Spec (.of F))) := by
    cases he
    rfl
  exact h _ _ (finitePointMap_algHom ε.toAlgHom q a)

/-- Actual diagonal transfer of each rational graph is invariant under presentation. -/
theorem corestriction_graphSymbol_algEquiv (ε : E ≃ₐ[k] F) (q : ℕ) (a : Fin q → Eˣ) :
    corestriction (k := k) q (graphSymbol E q a) =
      corestriction (k := k) q
        (graphSymbol F q (fun i => Units.map ε.toRingHom.toMonoidHom (a i))) := by
  rw [corestriction_graphSymbol, corestriction_graphSymbol, pointPushforward_graph_algEquiv ε]

/-- Actual transfer of every Milnor class agrees across algebra presentations. -/
theorem corestriction_rawSymbol_algEquiv (ε : E ≃ₐ[k] F) (q : ℕ) (x : MilnorKTheory E q) :
    corestriction (k := k) q (rawSymbol E q x) =
      corestriction (k := k) q (rawSymbol F q (milnorKTheoryMap ε.toRingHom q x)) := by
  have h : (corestriction (k := k) (E := E) q).comp (rawSymbol E q) =
      (corestriction (k := k) (E := F) q).comp
        ((rawSymbol F q).comp (milnorKTheoryMap ε.toRingHom q).toAddMonoidHom) := by
    apply milnorKTheory_addHom_ext
    intro a
    simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, rawSymbol_symbol,
      milnorKTheoryMap_tupleSymbol, Function.comp_def] using
      corestriction_graphSymbol_algEquiv ε q a
  exact DFunLike.congr_fun h x

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of F))) AddCommGrpCat.{u + 1})]

/-- Presentation transport also holds on the original derived diagonal groups. -/
theorem integralCorestriction_motivicSymbol_algEquiv (ε : E ≃ₐ[k] F) (q : ℕ)
    (x : MilnorKTheory E q) :
    integralCorestriction (k := k) q (motivicSymbol E q x) =
      integralCorestriction (k := k) q (motivicSymbol F q (milnorKTheoryMap ε.toRingHom q x)) := by
  apply (motivicRawBaseEvaluationComparison k q q).injective
  rw [integralCorestriction_comparison, integralCorestriction_comparison,
    motivicSymbol_comparison, motivicSymbol_comparison, corestriction_rawSymbol_algEquiv ε]

end AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction

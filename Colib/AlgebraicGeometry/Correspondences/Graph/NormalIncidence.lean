/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.NormalComponents
public import Colib.AlgebraicGeometry.Correspondences.Graph.Incidence

/-!
# Graph incidence over normal disconnected schemes

Every actual graph component source projection is open. Its base-changed incidence
projection is therefore open as well. A support mapping into one actual component
has empty incidence with every distinct graph component. Together with the stronger
matching-component isomorphism of Graph.Incidence, these are the geometric inputs
for a later all-component unit argument, not the unit argument itself.

No global integrality, connectedness, nonemptiness, perfectness, or fixed field is
assumed. The hypotheses here are normality and local Noetherianity of the scheme
whose components are used. Smooth-over-a-field specialization is downstream.

References: Stacks Project Tags 0357 and 033N for normal component geometry;
MVW (2006), Lecture 1, Example 1.2 (printed p. 3), and the diagonal/composition
paragraphs (printed p. 4). Implementation provenance: `motivic_source_a6805c4`,
`Correspondences/Composition/Identity/Tor.lean` and `Identity/Units.lean`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- The actual graph component source projection is open, including disconnected sources. -/
theorem isOpenImmersion_integralComponentAt_graphMap_fst
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) [IsSeparated g]
    [IsLocallyNoetherian X] [IsNormal X] (t : genericPoints X) :
    IsOpenImmersion
      ((integralComponentAt (correspondenceGraphMap f g φ hφ t.val)).subschemeι ≫
        pullback.fst f g) := by
  obtain ⟨e, hf, _⟩ := exists_iso_integralComponentAt_graphMap f g φ hφ t.val
  let : IsOpenImmersion (integralComponentAt t.val).subschemeι :=
    isOpenImmersion_integralComponentAt_of_isNormal t
  have heq :
      (integralComponentAt (correspondenceGraphMap f g φ hφ t.val)).subschemeι ≫
        pullback.fst f g = e.inv ≫ (integralComponentAt t.val).subschemeι := by
    apply (cancel_epi e.hom).mp
    simpa only [Iso.hom_inv_id_assoc] using hf
  rw [heq]
  infer_instance

/-- The first actual graph incidence projection is open by base change. -/
theorem isOpenImmersion_correspondenceIncidence_fst_graphMap
    {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g) [IsSeparated h]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (z : pullback (C := Scheme) f g) (t : genericPoints Y) :
    IsOpenImmersion (pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt (correspondenceGraphMap g h ψ hψ t.val)).subschemeι ≫
        pullback.fst g h)) := by
  let := isOpenImmersion_integralComponentAt_graphMap_fst g h ψ hψ t
  infer_instance

/-- Different actual middle components give an empty graph incidence scheme. -/
theorem isEmpty_correspondenceIncidence_graphMap_of_ne
    {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g) [IsSeparated h]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (z : pullback (C := Scheme) f g) (s t : genericPoints Y) (hst : s ≠ t)
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆ closure {s.val}) :
    IsEmpty (correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ t.val)) := by
  have hd : Disjoint (closure {s.val} : Set Y) (closure {t.val}) :=
    disjoint_of_mem_irreducibleComponents_of_isNormal _ _ s.property t.property
      (fun heq => hst (genericPoints.component_injective (Subtype.ext heq)))
  apply Scheme.isEmpty_pullback
  rw [range_integralComponentAt_graphMap_fst]
  exact hd.mono_left hz

/-- The second actual left diagonal incidence projection is open by base change. -/
theorem isOpenImmersion_correspondenceIncidence_snd_diagonal
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f]
    [IsLocallyNoetherian X] [IsNormal X]
    (t : genericPoints X) (z : pullback (C := Scheme) f g) :
    IsOpenImmersion (pullback.snd
      ((integralComponentAt (correspondenceGraphMap f f (𝟙 X) (by simp) t.val)).subschemeι ≫
        pullback.snd f f)
      ((integralComponentAt z).subschemeι ≫ pullback.fst f g)) := by
  have hdiag := integralComponentAt_graphMap_snd f f (𝟙 X) (by simp) t.val
  simp only [Category.comp_id] at hdiag
  let : IsOpenImmersion
      ((integralComponentAt (correspondenceGraphMap f f (𝟙 X) (by simp) t.val)).subschemeι ≫
        pullback.snd f f) := by
    rw [hdiag]
    exact isOpenImmersion_integralComponentAt_graphMap_fst f f (𝟙 X) (by simp) t
  infer_instance

/-- A support in one source component has empty left incidence with every other diagonal
component.
-/
theorem isEmpty_correspondenceIncidence_diagonal_left_of_ne
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f]
    [IsLocallyNoetherian X] [IsNormal X]
    (z : pullback (C := Scheme) f g) (s t : genericPoints X) (hst : s ≠ t)
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ⊆ closure {s.val}) :
    IsEmpty (correspondenceIncidence f f g
      (correspondenceGraphMap f f (𝟙 X) (by simp) t.val) z) := by
  have hd : Disjoint (closure {s.val} : Set X) (closure {t.val}) :=
    disjoint_of_mem_irreducibleComponents_of_isNormal _ _ s.property t.property
      (fun heq => hst (genericPoints.component_injective (Subtype.ext heq)))
  apply Scheme.isEmpty_pullback
  rw [integralComponentAt_graphMap_snd, Category.comp_id,
    range_integralComponentAt_graphMap_fst]
  exact hd.symm.mono_right hz

end Stacks.Chow

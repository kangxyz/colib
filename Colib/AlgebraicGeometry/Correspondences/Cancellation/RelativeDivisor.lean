/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection
public import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Basic

/-!
# Signed principal cuts with finite support

Cut a support scheme by two global equations and push the whole zero cycles
to the original product. Each zero scheme is finite over the source, and its
generic points project to source generic points. The pushforward retains the
generic stalk lengths of the zero schemes and the residue degrees of the maps.
Postcomposition by a graph preserves the resulting signed correspondence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme AffineLineFiber

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
  (p : P ⟶ X.left) (g : P ⟶ Y.left) (h : p ≫ X.hom = g ≫ Y.hom)

local notation "Z₀(" s ")" => fiber (sectionToAffineLine (p ≫ X.hom) s) 0
local notation "i₀(" s ")" => inclusion (sectionToAffineLine (p ≫ X.hom) s) 0
local notation "p₀(" s ")" => i₀(s) ≫ p

/-- The two original projections restricted to the literal zero scheme. -/
def sectionCutSupportMap (s : Γ(P, ⊤)) : Z₀(s) ⟶ pullback X.hom Y.hom :=
  pullback.lift (p₀(s)) (i₀(s) ≫ g) (by simp only [Category.assoc, h])

@[reassoc (attr := simp)]
theorem sectionCutSupportMap_fst (s : Γ(P, ⊤)) :
    sectionCutSupportMap p g h s ≫ pullback.fst X.hom Y.hom = p₀(s) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sectionCutSupportMap_snd (s : Γ(P, ⊤)) :
    sectionCutSupportMap p g h s ≫ pullback.snd X.hom Y.hom = i₀(s) ≫ g :=
  pullback.lift_snd _ _ _

instance sectionCutSupportMap_isFinite (s : Γ(P, ⊤)) [IsFinite (p₀(s))] :
    IsFinite (sectionCutSupportMap p g h s) :=
  isFinite_spanMap (p₀(s)) (i₀(s) ≫ g) _

/-- A generic image under a finite map identifies the entire image of the
reduced component with an irreducible component of the target. -/
theorem range_integralComponentAt_mem_irreducibleComponents_of_image_generic
    {A B : Scheme.{u}} (f : A ⟶ B) [IsFinite f] (a : A) (ha : f a ∈ genericPoints B) :
    Set.range ((integralComponentAt a).subschemeι ≫ f) ∈ irreducibleComponents B := by
  rw [finiteCyclePushforward_range_integralComponentAt, coe_support_integralComponentAt]
  have hclosure : f.base '' closure ({a} : Set A) = closure ({f a} : Set B) := by
    simpa only [Set.image_singleton] using
      (f.isClosedMap.closure_image_eq_of_continuous f.continuous ({a} : Set A)).symm
  rwa [hclosure]

/-- Push the full fundamental cycle of the zero scheme to the finite
correspondence group, with the given generic-image condition. -/
def sectionCutCorrespondence (s : Γ(P, ⊤)) [IsFinite (p₀(s))]
    (hgen : ∀ a : genericPoints Z₀(s), p₀(s) a.val ∈ genericPoints X.left) :
    Cor.mk X ⟶ Cor.mk Y := by
  let : IsNoetherian Z₀(s) := isNoetherian_of_finiteType_of_isNoetherian (p₀(s))
  let m := sectionCutSupportMap p g h s
  let : IsFinite m := sectionCutSupportMap_isFinite p g h s
  refine ⟨finiteCyclePushforward m (AlgebraicCycle.fundamentalCycle Z₀(s)),
    finiteCyclePushforward_mem_finiteCorrespondences X.hom Y.hom m _
      (AlgebraicCycle.finite_support_fundamentalCycle Z₀(s)) ?_ ?_⟩
  · intro a _
    rw [Category.assoc, show m ≫ pullback.fst X.hom Y.hom = p₀(s) from
      sectionCutSupportMap_fst p g h s]
    infer_instance
  · intro a ha
    rw [Category.assoc, show m ≫ pullback.fst X.hom Y.hom = p₀(s) from
      sectionCutSupportMap_fst p g h s]
    exact range_integralComponentAt_mem_irreducibleComponents_of_image_generic (p₀(s)) a
      (hgen ⟨a, AlgebraicCycle.support_fundamentalCycle_subset Z₀(s) ha⟩)

/-- The native value uses the entire unreduced zero scheme. -/
theorem sectionCutCorrespondence_val (s : Γ(P, ⊤)) [IsFinite (p₀(s))]
    [IsNoetherian Z₀(s)]
    (hgen : ∀ a : genericPoints Z₀(s), p₀(s) a.val ∈ genericPoints X.left) :
    (sectionCutCorrespondence p g h s hgen).val =
      finiteCyclePushforward (sectionCutSupportMap p g h s)
        (AlgebraicCycle.fundamentalCycle Z₀(s)) :=
  rfl

/-- Composition with a target graph postcomposes the original cut map. -/
theorem sectionCutCorrespondence_comp_graph {Y' : SmoothSite (Spec (.of k))}
    (a : Y ⟶ Y') (s : Γ(P, ⊤)) [IsFinite (p₀(s))]
    (hgen : ∀ z : genericPoints Z₀(s), p₀(s) z.val ∈ genericPoints X.left) :
    sectionCutCorrespondence p g h s hgen ≫ (graphFunctor k).map a =
      sectionCutCorrespondence p (g ≫ a.left)
        (by rw [Category.assoc, MorphismProperty.Over.w, h]) s hgen := by
  classical
  let : IsNoetherian Z₀(s) := isNoetherian_of_finiteType_of_isNoetherian (p₀(s))
  let h' : p ≫ X.hom = (g ≫ a.left) ≫ Y'.hom :=
    by rw [Category.assoc, MorphismProperty.Over.w, h]
  let m := sectionCutSupportMap p g h s
  let m' := sectionCutSupportMap p (g ≫ a.left) h' s
  let : IsFinite m := sectionCutSupportMap_isFinite p g h s
  let : IsFinite m' := sectionCutSupportMap_isFinite p (g ≫ a.left) h' s
  have hmap : m ≫ pullback.map X.hom Y.hom X.hom Y'.hom
      (𝟙 X.left) a.left (𝟙 _) (by simp) (by simp) = m' := by
    apply pullback.hom_ext <;> simp [m, m', Category.assoc]
  have hadm : ∀ z : genericPoints Z₀(s), IsFiniteCorrespondencePoint X.hom Y.hom (m z.val) := by
    intro z
    apply isFiniteCorrespondencePoint_finiteMap X.hom Y.hom m z.val
    · simp only [Category.assoc, m, sectionCutSupportMap_fst]
      infer_instance
    · change Set.range (((integralComponentAt z.val).subschemeι ≫ m) ≫
        pullback.fst X.hom Y.hom) ∈ irreducibleComponents X.left
      rw [Category.assoc, show m ≫ pullback.fst X.hom Y.hom = p₀(s) from
        sectionCutSupportMap_fst p g h s]
      exact range_integralComponentAt_mem_irreducibleComponents_of_image_generic (p₀(s)) z.val
        (hgen z)
  obtain ⟨β, hβ, hpost⟩ := exists_graph_factorization_of_generic_support_map
    X.hom Y.hom Y'.hom a.left (MorphismProperty.Over.w a)
    (finite_genericPoints k (Cor.mk Y)) m m' hmap
    (AlgebraicCycle.fundamentalCycle_genericPoints_finite Z₀(s))
    (fun z => ((Module.length (Z₀(s).presheaf.stalk z.val)
      (Z₀(s).presheaf.stalk z.val)).toNat : ℤ)) hadm
  have hb : β = sectionCutCorrespondence p g h s hgen := Subtype.ext hβ
  rw [hb] at hpost
  exact Subtype.ext hpost

/-- The finite correspondence of the numerator cut minus the denominator cut. -/
def signedSectionCutCorrespondence (s t : Γ(P, ⊤)) [IsFinite (p₀(s))] [IsFinite (p₀(t))]
    (hs : ∀ a : genericPoints Z₀(s), p₀(s) a.val ∈ genericPoints X.left)
    (ht : ∀ a : genericPoints Z₀(t), p₀(t) a.val ∈ genericPoints X.left) :
    Cor.mk X ⟶ Cor.mk Y :=
  sectionCutCorrespondence p g h s hs - sectionCutCorrespondence p g h t ht

/-- The two full zero cycles retain their signs under graph postcomposition. -/
theorem signedSectionCutCorrespondence_comp_graph {Y' : SmoothSite (Spec (.of k))}
    (a : Y ⟶ Y') (s t : Γ(P, ⊤)) [IsFinite (p₀(s))] [IsFinite (p₀(t))]
    (hs : ∀ z : genericPoints Z₀(s), p₀(s) z.val ∈ genericPoints X.left)
    (ht : ∀ z : genericPoints Z₀(t), p₀(t) z.val ∈ genericPoints X.left) :
    signedSectionCutCorrespondence p g h s t hs ht ≫ (graphFunctor k).map a =
      signedSectionCutCorrespondence p (g ≫ a.left)
        (by rw [Category.assoc, MorphismProperty.Over.w, h]) s t hs ht := by
  simp only [signedSectionCutCorrespondence, Preadditive.sub_comp,
    sectionCutCorrespondence_comp_graph]

end AlgebraicGeometry.Cor

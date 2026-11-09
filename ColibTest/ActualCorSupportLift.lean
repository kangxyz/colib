/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Nisnevich.GeneratorLift

/-! Genuine whole-support factorization consumers. The support pullback has no
reducedness or flatness hypothesis, and the field has no perfectness hypothesis.
 -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {X Y U V : Scheme.SmoothSite (Spec (.of k))}
  (a : pullback (C := Scheme) X.hom Y.hom) (ha : IsFiniteCorrespondencePoint X.hom Y.hom a)
  (g : U ⟶ X) (q : V ⟶ Y)
  (b : pullback ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom)
      g.left ⟶ V.left)
  (hb : b ≫ q.left = pullback.fst
    ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left ≫
      (integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom)

include b hb in
example : ∃ β : Cor.mk U ⟶ Cor.mk V,
    β ≫ (graphFunctor k).map q =
      (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha 1 :=
  exists_graph_factorization_of_support_lift k a ha g q b hb

include b hb in
example : ∃ β : Cor.mk U ⟶ Cor.mk V,
    β ≫ (graphFunctor k).map q =
      (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha (-3) :=
  exists_graph_factorization_of_support_lift_signed k a ha g q b hb (-3)

example {W : Scheme.SmoothSite (Spec (.of k))}
    (a : pullback (C := Scheme) W.hom Y.hom) (ha : IsFiniteCorrespondencePoint W.hom Y.hom a)
    [IsOpenImmersion q.left]
    (hA : Set.range ((integralComponentAt a).subschemeι ≫ pullback.snd W.hom Y.hom) ⊆
      Set.range q.left) :
    ∃ β : Cor.mk W ⟶ Cor.mk V,
      β ≫ (graphFunctor k).map q = singleFiniteCorrespondence W.hom Y.hom a ha 1 :=
  exists_graph_factorization_of_range_subset k a ha q hA

end AlgebraicGeometry.Cor

section GenericCycle

variable {k : Type u} [Field k] {X Y Z A : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  (q : Y ⟶ Z) (hq : q ≫ h = g) (hY : (genericPoints Y).Finite)
  (m : A ⟶ pullback f g) [IsFinite m] (j : A ⟶ pullback f h) [IsFinite j]
  (hmj : m ≫ pullback.map f g f h (𝟙 X) q (𝟙 _) (by simp)
    (by simpa using hq.symm) = j)

include hmj in
example (hA : (genericPoints A).Finite) (c : genericPoints A → ℤ)
    (ha : ∀ a : genericPoints A, IsFiniteCorrespondencePoint f g (m a.val)) :
    ∃ β : finiteCorrespondences f g,
      β.val = finiteCyclePushforward m (AlgebraicCycle.ofGenericCoefficients hA c) ∧
      (incidenceTorPairing f g h β (graphCorrespondenceOfComponents g h q hq hY)).val =
        finiteCyclePushforward j (AlgebraicCycle.ofGenericCoefficients hA c) :=
  exists_graph_factorization_of_generic_support_map f g h q hq hY m j hmj hA c ha

end GenericCycle

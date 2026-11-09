/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleGenericImageSupport

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)

example : UniversallyOpen ((integralComponentAt z).subschemeι ≫ pullback.fst f g) :=
  universallyOpen_finiteCorrespondenceProjection_of_smooth f g z hz

example : (genericPoints (correspondenceTripleIncidence f g h i z w v)).Finite :=
  finite_genericPoints_correspondenceTripleIncidence_of_smooth f g h i z w v hw hv

example (t : correspondenceTripleIncidence f g h i z w v)
    (ht : t ∈ genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    correspondenceTripleToLeftImageIncidence f g h i z w v t ∈
      genericPoints (correspondenceLeftImageIncidence f g h i z w v) :=
  mem_genericPoints_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw hv t ht

example {A B : Scheme.{u}} (p : A ⟶ B) [IsFinite p] (a : A)
    (ha : p a ∈ genericPoints B) : a ∈ genericPoints A :=
  mem_genericPoints_of_finite_image p a ha

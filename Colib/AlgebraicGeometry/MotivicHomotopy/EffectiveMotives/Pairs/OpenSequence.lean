/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Transfer
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.OpenImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # The transfer short exact sequence of an open pair -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))
local notation "R" => smoothTransferRepresentable k

/-- Use the native transfer abelian structure for the original cokernel sequence. -/
local instance instAbelianOpenSequence : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The transfer representable sequence of an open and its quotient. -/
abbrev transferPairSequence (A : Arrow Sm(k)) : ShortComplex (SheafWithTransfers.{u + 1} k) :=
  ShortComplex.mk ((R).map A.hom) ((transferPairProjection k).app A) (cokernel.condition _)

/-- The original transfer representable sequence of an open pair is short exact. -/
theorem transferPairSequence_shortExact {U X : Sm(k)} (j : U ⟶ X)
    [IsOpenImmersion j.left] : (transferPairSequence k (Arrow.mk j)).ShortExact := by
  let f := (R).map j
  have hm : Mono f := mono_transferRepresentable_map_openImmersion k j
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f) hm
    (inferInstanceAs (Epi (cokernel.π f)))

/-- The morphism of transfer sequences induced by an original map of pairs. -/
def transferPairSequenceMap {A B : Arrow Sm(k)} (φ : A ⟶ B) :
    transferPairSequence k A ⟶ transferPairSequence k B :=
  ShortComplex.homMk ((R).map φ.left) ((R).map φ.right)
    ((transferPairCokernelFunctor k).map φ)
    (by
      change (R).map φ.left ≫ (R).map B.hom = (R).map A.hom ≫ (R).map φ.right
      rw [← Functor.map_comp, ← Functor.map_comp, Arrow.w φ])
    ((transferPairProjection k).naturality φ)

end AlgebraicGeometry.MotivicHomotopy

/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatIdealProduct
public import Colib.AlgebraicGeometry.Correspondences.Graph.WholeFiniteFlatEndpoint

/-!
# Actual product-divisor span additivity

The already proved whole-support ideal-product cycle identity is pushed along
the original finite ambient map. The output is an equality of the existing
finite-flat span correspondences. It is a supplier for signed pole cancellation,
not an unconditional identity for arbitrary zero loci.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open Scheme

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))} {C : Scheme.{u}}
  (m : C ⟶ pullback X.hom Y.hom) [IsFinite m]
  (I J K : C.IdealSheafData)
  [IsFinite (I.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)]
  [IsFinite (J.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)]
  [IsFinite (K.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)]
  [Flat (I.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)]
  [Flat (J.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)]
  [Flat (K.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)]

/-- Native finite-flat spans of a genuine ideal product add with every original
scheme-theoretic multiplicity; the second factor is actually regular. -/
theorem ofFiniteFlatSpan_add_of_ideal_product
    (hI : IsLocallyPrincipal I) (hJ : IsEffectiveCartierDivisor J) (hK : K = I * J) :
    ofFiniteFlatSpan (K.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)
      (K.subschemeι ≫ m ≫ pullback.snd X.hom Y.hom)
      (by simp only [Category.assoc, pullback.condition]) =
    ofFiniteFlatSpan (I.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)
      (I.subschemeι ≫ m ≫ pullback.snd X.hom Y.hom)
      (by simp only [Category.assoc, pullback.condition]) +
    ofFiniteFlatSpan (J.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)
      (J.subschemeι ≫ m ≫ pullback.snd X.hom Y.hom)
      (by simp only [Category.assoc, pullback.condition]) := by
  haveI := isNoetherian_of_finiteType (I.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)
  haveI := isNoetherian_of_finiteType (J.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)
  haveI := isNoetherian_of_finiteType (K.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)
  have hcycle := finiteCyclePushforward_fundamentalCycle_add_of_ideal_product
    (m ≫ pullback.fst X.hom Y.hom) I J K hI hJ hK
  apply Subtype.ext
  simp only [AddSubgroup.coe_add]
  rw [ofFiniteFlatSpan_val, ofFiniteFlatSpan_val, ofFiniteFlatSpan_val]
  have hl (T : C.IdealSheafData) :
      pullback.lift (T.subschemeι ≫ m ≫ pullback.fst X.hom Y.hom)
        (T.subschemeι ≫ m ≫ pullback.snd X.hom Y.hom)
        (by simp only [Category.assoc, pullback.condition]) = T.subschemeι ≫ m := by
    apply pullback.hom_ext <;> simp
  simp only [hl]
  rw [← finiteCyclePushforward_comp_apply, ← finiteCyclePushforward_comp_apply,
    ← finiteCyclePushforward_comp_apply, hcycle, map_add]

end AlgebraicGeometry.Cor

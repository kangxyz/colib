/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.IdealProduct
public import Colib.AlgebraicGeometry.Scheme.ForgetBaseProduct

/-! # Whole ideal-product spans on a relative product -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {S X Y : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t] (q : X ⟶ S) (r : Y ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]

omit [IsSeparated t] in
/-- The whole ideal support with the two actual projections of the relative product. -/
def retainedIdealSpan (I : (pullback q r).IdealSheafData)
    [IsFinite (I.subschemeι ≫ pullback.fst q r)] [Flat (I.subschemeι ≫ pullback.fst q r)] :
    Stacks.Chow.finiteCorrespondences (q ≫ t) (r ≫ t) := by
  let f := I.subschemeι ≫ pullback.fst q r
  let g := I.subschemeι ≫ pullback.snd q r
  let h : f ≫ q ≫ t = g ≫ r ≫ t := by
    simp only [f, g, Category.assoc, pullback.condition_assoc]
  let z := pullback.lift f g h
  let : IsNoetherian X := isNoetherian_of_finiteType_of_isNoetherian (q ≫ t)
  let : IsFinite f := inferInstanceAs (IsFinite (I.subschemeι ≫ pullback.fst q r))
  let : Flat f := inferInstanceAs (Flat (I.subschemeι ≫ pullback.fst q r))
  let : IsNoetherian I.subscheme := isNoetherian_of_finiteType_of_isNoetherian f
  have hf : z ≫ pullback.fst (q ≫ t) (r ≫ t) = f := pullback.lift_fst _ _ _
  let : IsFinite (z ≫ pullback.fst (q ≫ t) (r ≫ t)) := hf.symm ▸ ‹IsFinite f›
  let : Flat (z ≫ pullback.fst (q ≫ t) (r ≫ t)) := hf.symm ▸ ‹Flat f›
  let : IsFinite z := IsFinite.of_comp z (pullback.fst (q ≫ t) (r ≫ t))
  exact Stacks.Chow.finiteFlatSpanFundamental (q ≫ t) (r ≫ t) z

local notation "span[" I "]" => retainedIdealSpan t q r I

omit [IsSeparated (q ≫ t)] [QuasiCompact (r ≫ t)] in
/-- The existing ideal-product span theorem on the literal retained product. -/
theorem retainedSpan_add_of_ideal_product (I J K : (pullback q r).IdealSheafData)
    [IsFinite (I.subschemeι ≫ pullback.fst q r)] [Flat (I.subschemeι ≫ pullback.fst q r)]
    [IsFinite (J.subschemeι ≫ pullback.fst q r)] [Flat (J.subschemeι ≫ pullback.fst q r)]
    [IsFinite (K.subschemeι ≫ pullback.fst q r)] [Flat (K.subschemeι ≫ pullback.fst q r)]
    (hI : IsLocallyPrincipal I) (hJ : IsEffectiveCartierDivisor J) (hK : K = I * J) :
    span[K] = span[I] + span[J] := by
  let m := forgetBaseProductMap t q r
  let : IsClosedImmersion m := inferInstanceAs (IsClosedImmersion (forgetBaseProductMap t q r))
  let : IsFinite m := inferInstance
  let : IsNoetherian X := isNoetherian_of_finiteType_of_isNoetherian (q ≫ t)
  let := isNoetherian_of_finiteType_of_isNoetherian (I.subschemeι ≫ pullback.fst q r)
  let := isNoetherian_of_finiteType_of_isNoetherian (J.subschemeι ≫ pullback.fst q r)
  let := isNoetherian_of_finiteType_of_isNoetherian (K.subschemeι ≫ pullback.fst q r)
  have hmf : m ≫ pullback.fst (q ≫ t) (r ≫ t) = pullback.fst q r :=
    forgetBaseProductMap_fst t q r
  have hms : m ≫ pullback.snd (q ≫ t) (r ≫ t) = pullback.snd q r :=
    forgetBaseProductMap_snd t q r
  have hVal (T : (pullback q r).IdealSheafData) [IsNoetherian T.subscheme]
      [IsFinite (T.subschemeι ≫ pullback.fst q r)] [Flat (T.subschemeι ≫ pullback.fst q r)] :
      (retainedIdealSpan t q r T).val =
        finiteCyclePushforward (T.subschemeι ≫ m)
          (AlgebraicCycle.fundamentalCycle T.subscheme) := by
    let f := T.subschemeι ≫ pullback.fst q r
    let g := T.subschemeι ≫ pullback.snd q r
    let h : f ≫ q ≫ t = g ≫ r ≫ t := by
      simp only [f, g, Category.assoc, pullback.condition_assoc]
    let z := pullback.lift f g h
    have hz : z = T.subschemeι ≫ m := by
      apply pullback.hom_ext
      · simp only [z, pullback.lift_fst, Category.assoc, hmf, f]
      · simp only [z, pullback.lift_snd, Category.assoc, hms, g]
    let : IsFinite z := hz.symm ▸ inferInstanceAs (IsFinite (T.subschemeι ≫ m))
    have hcongr {D E : Scheme.{u}} {i j : D ⟶ E} [IsFinite i] [IsFinite j]
        (h : i = j) (c : AlgebraicCycle D ℤ) :
        finiteCyclePushforward i c = finiteCyclePushforward j c := by
      subst j
      rfl
    exact hcongr hz _
  have hcycle := finiteCyclePushforward_fundamentalCycle_add_of_ideal_product
    (pullback.fst q r) I J K hI hJ hK
  apply Subtype.ext
  change (span[K]).val = (span[I]).val + (span[J]).val
  rw [hVal K, hVal I, hVal J, ← finiteCyclePushforward_comp_apply,
    ← finiteCyclePushforward_comp_apply, ← finiteCyclePushforward_comp_apply, hcycle, map_add]

end AlgebraicGeometry.Cor

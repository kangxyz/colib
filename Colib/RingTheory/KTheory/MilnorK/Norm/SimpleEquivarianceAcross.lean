/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.ChartInversionMap
public import Colib.RingTheory.KTheory.MilnorK.Norm.OriginResidueFields
public import Colib.RingTheory.KTheory.MilnorK.Norm.PolynomialResidueMap
public import Colib.RingTheory.KTheory.MilnorK.Residue.UnramifiedMapAcross
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.SimpleNorm

/-!
# Simple Milnor norm equivariance in independent universes

The actual coefficient isomorphism of polynomial quotients commutes with the native simple
Milnor norm. The specified uniformizer maps exactly to the target polynomial, so the finite
residue comparison is unramified. Pulling each target closed point back through the inverse
coefficient isomorphism transports a single-residue lift. The native negative infinity-residue
formula then identifies the original norms, with their original sign and quotient models.

The whole-ring transport is `milnorKRingMapLift`, whose restriction to each native homogeneous
group is `milnorKTheoryMap`. No characteristic or separability hypothesis is imposed.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u v w z

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
  isDiscreteValuationRing_localizationAtPrime_polynomial

/-- Composition of the universal ring transport, with three independent field universes. -/
theorem milnorKRingMapLift_comp_apply
    {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
    (f : k →+* K) (g : K →+* L) (x : MilnorKRing k) :
    milnorKRingMapLift g (milnorKRingMapLift f x) =
      milnorKRingMapLift (g.comp f) x := by
  let lhs := (milnorKRingMapLift g).toAddMonoidHom.comp
    (milnorKRingMapLift f).toAddMonoidHom
  let rhs := (milnorKRingMapLift (g.comp f)).toAddMonoidHom
  have hgen (l : List kˣ) :
      milnorKSymbolProd k l ∈ AddMonoidHom.eqLocus lhs rhs := by
    change milnorKRingMapLift g (milnorKRingMapLift f (milnorKSymbolProd k l)) =
      milnorKRingMapLift (g.comp f) (milnorKSymbolProd k l)
    simp only [milnorKRingMapLift_symbolProd, List.map_map]
    rfl
  exact mem_of_forall_milnorKSymbolProd_mem (H := AddMonoidHom.eqLocus lhs rhs) hgen x

/-- The specified-uniformizer unramified square on the whole native Milnor ring. -/
theorem dvrMilnorShiftMap_shift_map_across
    {R : Type u} {S : Type v}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {F : Type w} {E : Type z} [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
    (j : R →+* S) [IsLocalHom j] (f : F →+* E)
    (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
    {π : R} (hπ : Irreducible π) (hjπ : Irreducible (j π))
    (y : MilnorKRing F) :
    milnorKRingMapLift (IsLocalRing.ResidueField.map j)
        (MilnorKShift.shift (dvrMilnorShiftMap hπ y)) =
      MilnorKShift.shift (dvrMilnorShiftMap hjπ (milnorKRingMapLift f y)) := by
  let lhs := (milnorKRingMapLift (IsLocalRing.ResidueField.map j)).toAddMonoidHom.comp
    ((MilnorKShift.shiftHom (IsLocalRing.ResidueField R)).comp
      (dvrMilnorShiftMap (F := F) hπ).toAddMonoidHom)
  let rhs := ((MilnorKShift.shiftHom (IsLocalRing.ResidueField S)).comp
      (dvrMilnorShiftMap (F := E) hjπ).toAddMonoidHom).comp
    (milnorKRingMapLift f).toAddMonoidHom
  have hgen (l : List Fˣ) :
      milnorKSymbolProd F l ∈ AddMonoidHom.eqLocus lhs rhs := by
    change milnorKRingMapLift (IsLocalRing.ResidueField.map j)
        (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))) =
      MilnorKShift.shift (dvrMilnorShiftMap hjπ
        (milnorKRingMapLift f (milnorKSymbolProd F l)))
    simpa only [milnorKRingMapLift_symbolProd] using
      dvrMilnorShiftMap_shift_symbolProd_map_across j f hf hπ hjπ l
  exact mem_of_forall_milnorKSymbolProd_mem (H := AddMonoidHom.eqLocus lhs rhs) hgen y

private theorem dvrMilnorShiftMap_eq_of_uniformizer_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
    {π π' : R} (h : π = π') (hπ : Irreducible π) (hπ' : Irreducible π') :
    dvrMilnorShiftMap (F := F) hπ = dvrMilnorShiftMap (F := F) hπ' := by
  subst π'
  rfl

variable {k : Type u} {K : Type v} [Field k] [Field K]

/-- At an irreducible coefficient image, finite residue commutes with the literal quotient
map. The actual uniformizer is preserved, so no multiplicity or unit correction occurs. -/
theorem monicIrreducibleResidue_map_of_poly_eq_map_across
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K e)
    (hq : poly q = (poly p).map φ) (y : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue q
        (milnorKRingMapLift (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) =
      milnorKRingMapLift (AdjoinRoot.map φ (poly p) (poly q) (hq ▸ dvd_rfl))
        (monicIrreducibleResidue p y) := by
  let P : Ideal k[X] := Ideal.span {poly p}
  let Q : Ideal K[X] := Ideal.span {poly q}
  let hqp : poly q ∣ (poly p).map φ := hq ▸ dvd_rfl
  let hPQ : P = Q.comap (Polynomial.mapRingHom φ) :=
    (Polynomial.span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
      (irreducible p) (irreducible q).not_isUnit hqp).symm
  let j : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (Polynomial.mapRingHom φ) hPQ
  let Φ : RatFunc k →+* RatFunc K := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
  have hf (r : Localization.AtPrime P) :
      Φ (algebraMap (Localization.AtPrime P) (RatFunc k) r) =
        algebraMap (Localization.AtPrime Q) (RatFunc K) (j r) :=
    ratFunc_mapRingHom_algebraMap_localizationAtPrime φ P Q hPQ r
  have hj : j (algebraMap k[X] (Localization.AtPrime P) (poly p)) =
      algebraMap K[X] (Localization.AtPrime Q) (poly q) := by
    dsimp [j]
    rw [Localization.localRingHom_to_map]
    exact congrArg (algebraMap K[X] (Localization.AtPrime Q)) hq.symm
  have hjπ : Irreducible (j (algebraMap k[X] (Localization.AtPrime P) (poly p))) := by
    rw [hj]
    exact irreducible_algebraMap_self (p := poly q)
  have hs := dvrMilnorShiftMap_shift_map_across j Φ hf
    (irreducible_algebraMap_self (p := poly p)) hjπ y
  rw [dvrMilnorShiftMap_eq_of_uniformizer_eq hj hjπ
    (irreducible_algebraMap_self (p := poly q))] at hs
  let eP := (quotientRingEquivResidueField P).symm.toRingHom
  let eQ := (quotientRingEquivResidueField Q).symm.toRingHom
  let κ := IsLocalRing.ResidueField.map j
  let a : (k[X] ⧸ P) →+* (K[X] ⧸ Q) := AdjoinRoot.map φ (poly p) (poly q) hqp
  let β : MilnorKRing P.ResidueField :=
    MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
      (irreducible_algebraMap_self (p := poly p)) y)
  have hd : eQ.comp κ = a.comp eP :=
    quotientRingEquivResidueField_symm_comp_residueField_map_eq_comp_symm φ p q hqp
  simp only [monicIrreducibleResidue_apply, ← milnorKRingMapLift_eq]
  rw [← hs]
  change milnorKRingMapLift eQ (milnorKRingMapLift κ β) =
    milnorKRingMapLift a (milnorKRingMapLift eP β)
  exact (milnorKRingMapLift_comp_apply κ eQ β).trans
    ((congrArg (fun f : P.ResidueField →+* (K[X] ⧸ Q) => milnorKRingMapLift f β) hd).trans
      (milnorKRingMapLift_comp_apply eP a β).symm)

/-- The origin uniformizer is exactly `X` under coefficient extension in independent
universes; the whole-ring shift commutes with its actual residue-field map. -/
theorem dvrMilnorShiftMap_shift_mapRingHom_at_origin_across
    (φ : k →+* K) (y : MilnorKRing (RatFunc k)) :
    MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc K)
        (irreducible_algebraMap_X (k := K))
        (milnorKRingMapLift (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y)) =
      milnorKRingMapLift
        (IsLocalRing.ResidueField.map
          (Localization.localRingHom (Ideal.span ({X} : Set k[X]))
            (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
            (Polynomial.span_X_comap_mapRingHom φ).symm))
        (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
          (irreducible_algebraMap_X (k := k)) y)) := by
  let P : Ideal k[X] := Ideal.span {X}
  let Q : Ideal K[X] := Ideal.span {X}
  let hPQ : P = Q.comap (Polynomial.mapRingHom φ) :=
    (Polynomial.span_X_comap_mapRingHom φ).symm
  let j : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (Polynomial.mapRingHom φ) hPQ
  let Φ : RatFunc k →+* RatFunc K := RatFunc.mapRingHom (Polynomial.mapRingHom φ)
    (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
  have hf (r : Localization.AtPrime P) :
      Φ (algebraMap (Localization.AtPrime P) (RatFunc k) r) =
        algebraMap (Localization.AtPrime Q) (RatFunc K) (j r) :=
    ratFunc_mapRingHom_algebraMap_localizationAtPrime φ P Q hPQ r
  have hj : j (algebraMap k[X] (Localization.AtPrime P) X) =
      algebraMap K[X] (Localization.AtPrime Q) X := localRingHom_algebraMap_X φ
  have hjπ : Irreducible (j (algebraMap k[X] (Localization.AtPrime P) X)) := by
    rw [hj]
    exact irreducible_algebraMap_X (k := K)
  have hs := dvrMilnorShiftMap_shift_map_across j Φ hf
    (irreducible_algebraMap_X (k := k)) hjπ y
  rw [dvrMilnorShiftMap_eq_of_uniformizer_eq hj hjπ
    (irreducible_algebraMap_X (k := K))] at hs
  exact hs.symm

/-- The original infinity residue commutes with the coefficient map in independent
universes. The original chart inversion and origin dictionary introduce no extra sign. -/
theorem infinityResidueRing_mapRingHom_across
    (φ : k →+* K) (y : MilnorKRing (RatFunc k)) :
    infinityResidueRing K
        (milnorKRingMapLift (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) =
      milnorKRingMapLift φ (infinityResidueRing k y) := by
  simp only [infinityResidueRing_apply, ← milnorKRingMapLift_eq]
  rw [milnorKRingMapLift_comp_apply,
    AlgebraicGeometry.projectiveLineChartInversion_comp_mapRingHom,
    ← milnorKRingMapLift_comp_apply,
    dvrMilnorShiftMap_shift_mapRingHom_at_origin_across,
    milnorKRingMapLift_comp_apply]
  change milnorKRingMapLift
      ((residueFieldAtOriginEquiv K).symm.toRingHom.comp
        (IsLocalRing.ResidueField.map
          (Localization.localRingHom (Ideal.span ({X} : Set k[X]))
            (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
            (Polynomial.span_X_comap_mapRingHom φ).symm))) _ =
    milnorKRingMapLift φ
      (milnorKRingMapLift (residueFieldAtOriginEquiv k).symm.toRingHom _)
  rw [residueFieldAtOriginEquiv_symm_comp_residueField_map,
    ← milnorKRingMapLift_comp_apply]

/-- A coefficient isomorphism transports the original single-residue predicate. Each target
closed point is the coefficient image of its pullback through the inverse isomorphism. -/
theorem IsSingleResidueLift.map_ringEquiv_across
    (σ : k ≃+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K d)
    (hq : poly q = (poly p).map σ.toRingHom)
    {x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})}
    {y : MilnorKRing (RatFunc k)} (hy : IsSingleResidueLift p x y) :
    IsSingleResidueLift q
      (milnorKRingMapLift
        (AdjoinRoot.map σ.toRingHom (poly p) (poly q) (hq ▸ dvd_rfl)) x)
      (milnorKRingMapLift (RatFunc.mapRingHom (Polynomial.mapRingHom σ.toRingHom)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom σ.toRingHom)) y) := by
  refine ⟨?_, ?_⟩
  · rw [monicIrreducibleResidue_map_of_poly_eq_map_across σ.toRingHom p q hq, hy.1]
  · intro e r hr
    let s : MonicIrreducibleOfDegree k e :=
      ⟨(poly r).map σ.symm.toRingHom, (monic r).map _, by
        change Irreducible (Polynomial.mapEquiv σ.symm (poly r))
        rw [MulEquiv.irreducible_iff]
        exact irreducible r, by
        rw [Polynomial.natDegree_map, natDegree_eq]⟩
    have hs : poly r = (poly s).map σ.toRingHom := by
      ext n
      simp [s, poly]
    have hsp : poly s ≠ poly p := by
      intro h
      apply hr
      rw [hs, h, ← hq]
    rw [monicIrreducibleResidue_map_of_poly_eq_map_across σ.toRingHom s r hs,
      hy.2 e s hsp, map_zero]

/-- The actual native simple norm commutes with a coefficient isomorphism between fields in
independent universes and the literal induced map on their polynomial quotients. -/
theorem simpleMilnorNorm_map_of_poly_eq_map_across
    (σ : k ≃+* K) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree K d)
    (hq : poly q = (poly p).map σ.toRingHom)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMapLift σ.toRingHom (simpleMilnorNorm p x) =
      simpleMilnorNorm q (milnorKRingMapLift
        (AdjoinRoot.map σ.toRingHom (poly p) (poly q) (hq ▸ dvd_rfl)) x) := by
  obtain ⟨y, hy⟩ := exists_isSingleResidueLift_ring' p x
  have hmap := hy.map_ringEquiv_across σ p q hq
  rw [simpleMilnorNorm_eq hy, simpleMilnorNorm_eq hmap, map_neg,
    infinityResidueRing_mapRingHom_across]

end Stacks.Chow

end

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Tor.ExteriorEuler.Length
public import Colib.RingTheory.Tor.ExteriorEuler.SpectralLength
public import Mathlib.Algebra.Homology.Bifunctor
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToMap
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex

/-!
# Euler characteristic of the exterior tensor total

Exactness of exterior tensoring over a field identifies the second page of the column
spectral sequence with the exterior tensor of the two homologies. Flat scalar extension
preserves the abutment and the homology. Finite-length dévissage then computes the Euler
characteristic with the localized residue tensor as a factor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace CochainComplex

universe u

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

local notation "c" => ComplexShape.up ℤ

/-- The bicomplex with `(p,q)` term `K^p ⊗[k] L^q` over the tensor product ring. -/
abbrev exteriorDouble (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : CochainComplex (ModuleCat.{u} B) ℤ) :
    HomologicalComplex₂ (ModuleCat.{u} (A ⊗[k] B)) c c :=
  (((ModuleCat.exteriorTensor (k := k)).mapBifunctorHomologicalComplex c c).obj K).obj L

variable (K : CochainComplex (ModuleCat.{u} A) ℤ) (L : CochainComplex (ModuleCat.{u} B) ℤ)

/-- Vertical cohomology is exterior tensor with the cohomology of the second complex. -/
def exteriorDoubleVerticalHomologyIso (q : ℤ) :
    (((homologyFunctor (ModuleCat.{u} (A ⊗[k] B)) c q).mapHomologicalComplex c).obj
        (exteriorDouble (k := k) K L)) ≅
      ((((ModuleCat.exteriorTensor (k := k) (A := A)).flip.obj (L.homology q)).mapHomologicalComplex
        c).obj K) := by
  refine Hom.isoOfComponents (fun p =>
    (L.sc q).mapHomologyIso ((ModuleCat.exteriorTensor (k := k) (B := B)).obj (K.X p))) ?_
  intro i j _
  symm
  change ShortComplex.homologyMap ((L.sc q).mapNatTrans
      ((ModuleCat.exteriorTensor (k := k) (B := B)).map (K.d i j))) ≫ _ = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The two successive homologies of the exterior tensor double complex are the exterior
tensor product of the two individual homologies, over `A ⊗[k] B`. -/
def exteriorDoubleSecondHomologyIso (p q : ℤ) :
    ((((homologyFunctor (ModuleCat.{u} (A ⊗[k] B)) c q).mapHomologicalComplex c).obj
        (exteriorDouble (k := k) K L)).homology p) ≅
      ModuleCat.exteriorTensorObj k (K.homology p) (L.homology q) :=
  (homologyFunctor _ c p).mapIso (exteriorDoubleVerticalHomologyIso (k := k) K L q) ≪≫
    (K.sc p).mapHomologyIso ((ModuleCat.exteriorTensor (k := k) (A := A)).flip.obj (L.homology q))

private theorem exteriorDouble_diagFinite (a b : ℤ)
    (hK : ∀ p, a < p → IsZero (K.X p)) (hL : ∀ q, b < q → IsZero (L.X q)) :
    ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero (((exteriorDouble (k := k) K L).X pq.1).X pq.2)}.Finite := by
  intro n
  refine ((Set.finite_Icc (n - b) a).image (fun p => (p, n - p))).subset ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hp : p ≤ a := le_of_not_gt fun h => hz
    (((ModuleCat.exteriorTensor (k := k) (A := A)).flip.obj (L.X q)).map_isZero (hK p h))
  have hq : q ≤ b := le_of_not_gt fun h => hz
    (((ModuleCat.exteriorTensor (k := k) (B := B)).obj (K.X p)).map_isZero (hL q h))
  exact ⟨p, ⟨by omega, hp⟩, Prod.ext rfl (show n - p = q by omega)⟩

variable {S : Type u} [CommRing S] [Algebra (A ⊗[k] B) S]

local notation "E" => (ModuleCat.extendScalars (algebraMap (A ⊗[k] B) S) :
  ModuleCat (A ⊗[k] B) ⥤ ModuleCat S)

/-- The exterior tensor total after the given scalar extension. -/
abbrev exteriorTotalBaseChange : CochainComplex (ModuleCat.{u} S) ℤ :=
  ((E).mapHomologicalComplex c).obj ((exteriorDouble (k := k) K L).total c)

variable [Module.Flat (A ⊗[k] B) S]

/-- The second page of the column spectral sequence for the base-changed exterior total
consists of the base-changed exterior products of the individual homology modules. -/
theorem exists_exteriorTotalBaseChange_spectralSequence (a b : ℤ)
    (hK : ∀ p, a < p → IsZero (K.X p)) (hL : ∀ q, b < q → IsZero (L.X q)) :
    ∃ F : CohomologicalSpectralSequence (ModuleCat.{u} S) 0,
      F.AbutsTo (fun n => (E).obj (((exteriorDouble (k := k) K L).total c).homology n)) ∧
        ∀ p q : ℤ, Nonempty ((F.page 2 zero_le_two).X (p, q) ≅
          (E).obj (ModuleCat.exteriorTensorObj k (K.homology p) (L.homology q))) := by
  let : PreservesFiniteLimits E := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (A ⊗[k] B) S))
  let D := exteriorDouble (k := k) K L
  let P := D.totalFiltration₁
  let F := CochainComplex.Filtered.spectralSequenceFunctor.obj P
  have hfin := exteriorDouble_diagFinite (k := k) K L a b hK hL
  have hF := CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite' P
    (D.isDegreewiseFinite_totalFiltration₁ hfin)
  obtain ⟨isoPage, hd⟩ := CochainComplex.Filtered.exists_pageIso_d P
  obtain ⟨-, -, h₂⟩ := D.exists_iso_pages_totalFiltration₁ _ (fun _ _ => rfl)
    _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl) F isoPage hd
  refine ⟨F.map E, hF.map E, fun p q => ?_⟩
  obtain ⟨e⟩ := h₂ p q
  exact ⟨(E).mapIso (e ≪≫ exteriorDoubleSecondHomologyIso (k := k) K L p q)⟩

variable [IsLocalRing A] [IsLocalRing B]

/-- The alternating cohomology length of the localized exterior total is the product of the
two alternating lengths and the length of the base-changed residue tensor. -/
theorem finsum_length_exteriorTotalBaseChange (a b : ℤ)
    (hK : ∀ p, a < p → IsZero (K.X p)) (hL : ∀ q, b < q → IsZero (L.X q))
    (hfK : ∀ p, IsFiniteLength A (K.homology p)) (hfL : ∀ q, IsFiniteLength B (L.homology q))
    (hsK : {p | ¬ IsZero (K.homology p)}.Finite) (hsL : {q | ¬ IsZero (L.homology q)}.Finite)
    (hfres : Module.length S ((E).obj (ModuleCat.exteriorTensorObj k
      (ModuleCat.of A (IsLocalRing.ResidueField A))
      (ModuleCat.of B (IsLocalRing.ResidueField B)))) ≠ ⊤) :
    (∀ n, IsFiniteLength S ((exteriorTotalBaseChange (k := k) (S := S) K L).homology n)) ∧
    {n | ¬ IsZero ((exteriorTotalBaseChange (k := k) (S := S) K L).homology n)}.Finite ∧
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) *
      ((Module.length S ((exteriorTotalBaseChange (k := k) (S := S) K L).homology n)).toNat : ℤ)) =
      (∑ᶠ p : ℤ, (p.negOnePow : ℤ) * ((Module.length A (K.homology p)).toNat : ℤ)) *
        (∑ᶠ q : ℤ, (q.negOnePow : ℤ) * ((Module.length B (L.homology q)).toNat : ℤ)) *
        ((Module.length S ((E).obj (ModuleCat.exteriorTensorObj k
          (ModuleCat.of A (IsLocalRing.ResidueField A))
          (ModuleCat.of B (IsLocalRing.ResidueField B))))).toNat : ℤ) := by
  classical
  let : PreservesFiniteLimits E := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (A ⊗[k] B) S))
  obtain ⟨F, hF, e⟩ :=
    exists_exteriorTotalBaseChange_spectralSequence (k := k) (S := S) K L a b hK hL
  let D := (exteriorDouble (k := k) K L).total c
  let lres := Module.length S ((E).obj (ModuleCat.exteriorTensorObj k
    (ModuleCat.of A (IsLocalRing.ResidueField A)) (ModuleCat.of B (IsLocalRing.ResidueField B))))
  let x : ℤ → ℤ := fun p => (p.negOnePow : ℤ) * (Module.length A (K.homology p)).toNat
  let y : ℤ → ℤ := fun q => (q.negOnePow : ℤ) * (Module.length B (L.homology q)).toNat
  have hlen (p q : ℤ) : Module.length S ((F.page 2 zero_le_two).X (p, q)) =
      Module.length A (K.homology p) * Module.length B (L.homology q) * lres :=
    ((e p q).some.toLinearEquiv.length_eq).trans
      (ModuleCat.length_extendScalars_exteriorTensor (k := k) (S := S) _ _ (hfK p) (hfL q))
  have hfin (pq : ℤ × ℤ) : Module.length S ((F.page 2 zero_le_two).X pq) ≠ ⊤ := by
    rcases pq with ⟨p, q⟩
    rw [hlen]
    exact WithTop.mul_ne_top (WithTop.mul_ne_top (Module.length_ne_top_iff.mpr (hfK p))
      (Module.length_ne_top_iff.mpr (hfL q))) hfres
  have hs (pq : ℤ × ℤ) (hpq : ¬ IsZero ((F.page 2 zero_le_two).X pq)) :
      pq ∈ {p | ¬ IsZero (K.homology p)} ×ˢ {q | ¬ IsZero (L.homology q)} := by
    rcases pq with ⟨p, q⟩
    refine ⟨fun hp => hpq ?_, fun hq => hpq ?_⟩
    · exact (ModuleCat.length_eq_zero_iff_isZero _).1 (by
        rw [hlen, (ModuleCat.length_eq_zero_iff_isZero _).2 hp, zero_mul, zero_mul])
    · exact (ModuleCat.length_eq_zero_iff_isZero _).1 (by
        rw [hlen, (ModuleCat.length_eq_zero_iff_isZero _).2 hq, mul_zero, zero_mul])
  have hsupport := (hsK.prod hsL).subset hs
  have habuts := hF.finsum_length_eq 2 zero_le_two hfin hsupport
  obtain ⟨hfinite, hsupport'⟩ := hF.finiteLength_and_support 2 zero_le_two hfin hsupport
  have he (n : ℤ) : (exteriorTotalBaseChange (k := k) (S := S) K L).homology n ≅
      (E).obj (D.homology n) := (D.sc n).mapHomologyIso E
  refine ⟨fun n => (he n).symm.toLinearEquiv.isFiniteLength (hfinite n),
    hsupport'.subset (fun n hn hz => hn (hz.of_iso (he n))), ?_⟩
  have hsupp : (Function.support (fun pq : ℤ × ℤ => x pq.1 * y pq.2)).Finite := by
    refine (hsK.prod hsL).subset ?_
    intro pq hpq
    refine ⟨fun hp => hpq ?_, fun hq => hpq ?_⟩
    · simp [x, (ModuleCat.length_eq_zero_iff_isZero _).2 hp]
    · simp [y, (ModuleCat.length_eq_zero_iff_isZero _).2 hq]
  change _ = (∑ᶠ p, x p) * (∑ᶠ q, y q) * (lres.toNat : ℤ)
  calc
    _ = ∑ᶠ n : ℤ, (n.negOnePow : ℤ) *
        ((Module.length S ((E).obj (D.homology n))).toNat : ℤ) := by
      refine finsum_congr fun n => ?_
      rw [(he n).toLinearEquiv.length_eq]
    _ = ∑ᶠ pq : ℤ × ℤ, ((pq.1 + pq.2).negOnePow : ℤ) *
        ((Module.length S ((F.page 2 zero_le_two).X pq)).toNat : ℤ) := habuts
    _ = (∑ᶠ pq : ℤ × ℤ, x pq.1 * y pq.2) * (lres.toNat : ℤ) := by
      rw [finsum_mul]
      refine finsum_congr fun ⟨p, q⟩ => ?_
      rw [hlen p q, ENat.toNat_mul, ENat.toNat_mul, Nat.cast_mul, Nat.cast_mul,
        Int.negOnePow_add, Units.val_mul]
      dsimp only [x, y]
      ring
    _ = _ := by
      rw [finsum_curry _ hsupp]
      have hpull (p : ℤ) : (∑ᶠ q, x p * y q) = x p * (∑ᶠ q, y q) := (mul_finsum y (x p)).symm
      simp only [hpull]
      rw [← finsum_mul x]

end CochainComplex

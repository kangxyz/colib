/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Tor.ExteriorEuler.Resolution
public import StacksFrontier.Homology.KFlat.ProjectiveResolution

/-!
# Euler product for exterior Tor

Over a field the Euler characteristic of Tor for exterior products multiplies,
with the base-changed residue tensor length retained. The statement uses categorical
Tor in every natural degree and assumes finite support and finite length on the two
input Tor families. The proof uses their native projective resolutions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open scoped TensorProduct

namespace ModuleCat.Tor

universe u

local notation "c" => ComplexShape.up ℤ

private theorem finsum_int_eq_finsum_neg_nat (f : ℤ → ℤ) (hf : ∀ n > 0, f n = 0) :
    (∑ᶠ n : ℤ, f n) = ∑ᶠ n : ℕ, f (-(n : ℤ)) := by
  let g : ℕ → ℤ := fun n => -(n : ℤ)
  have hg : Function.Injective g := fun _ _ h => Int.natCast_inj.mp (neg_injective h)
  change _ = ∑ᶠ n : ℕ, f (g n)
  rw [← finsum_mem_range hg, ← finsum_mem_univ]
  refine finsum_mem_inter_support_eq _ _ _ ?_
  ext n
  simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_univ, true_and, Function.mem_support]
  refine ⟨fun hn => ⟨?_, hn⟩, fun hn => hn.2⟩
  have hneg : n ≤ 0 := by
    by_contra h
    exact hn (hf n (by omega))
  obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat hneg
  exact ⟨m, hm.symm⟩

private theorem finsum_homology_eq_tor {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsStrictlyLE 0]
    (M N : ModuleCat.{u} R)
    (h : ∀ n : ℕ, K.homology (-(n : ℤ)) ≅ ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj M).obj N) :
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * ((Module.length R (K.homology n)).toNat : ℤ)) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        ((Module.length R (((CategoryTheory.Tor (ModuleCat.{u} R) n).obj M).obj N)).toNat : ℤ) := by
  rw [finsum_int_eq_finsum_neg_nat _ fun n hn => by
    have hz : IsZero (K.homology n) :=
      (K.sc n).isZero_homology_of_isZero_X₂ (K.isZero_of_isStrictlyLE 0 n hn)
    have : Subsingleton (K.homology n) := ModuleCat.subsingleton_of_isZero hz
    simp]
  refine finsum_congr fun n => ?_
  rw [Int.negOnePow_neg, Int.coe_negOnePow_natCast, (h n).toLinearEquiv.length_eq]

private def tensorLeftCochainTorIso {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (P : ProjectiveResolution N) (n : ℕ) :
    (((tensorLeft M).mapHomologicalComplex c).obj P.cochainComplex).homology (-(n : ℤ)) ≅
      ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj M).obj N :=
  (homologyFunctor _ c (-(n : ℤ))).mapIso
      (HomologicalComplex.mapHomologicalComplexExtendIso (tensorLeft M) P.complex
        ComplexShape.embeddingDownNat).symm ≪≫
    HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingDownNat (j := n) rfl ≪≫
    (P.isoLeftDerivedObj (tensorLeft M) n).symm

private theorem finite_homology_support_of_finite_tor {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsStrictlyLE 0]
    (M N : ModuleCat.{u} R)
    (h : ∀ n : ℕ, K.homology (-(n : ℤ)) ≅ ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj M).obj N)
    (hs : {n : ℕ | ¬ IsZero (((CategoryTheory.Tor (ModuleCat.{u} R) n).obj M).obj N)}.Finite) :
    {n : ℤ | ¬ IsZero (K.homology n)}.Finite := by
  refine (hs.image (fun n : ℕ => -(n : ℤ))).subset fun n hn => ?_
  have hn₀ : n ≤ 0 := le_of_not_gt fun hpos => hn
    ((K.sc n).isZero_homology_of_isZero_X₂ (K.isZero_of_isStrictlyLE 0 n hpos))
  obtain ⟨m, e⟩ := Int.exists_eq_neg_ofNat hn₀
  refine ⟨m, ?_, e.symm⟩
  rw [e] at hn
  exact fun hz => hn (hz.of_iso (h m))

variable {k A B S : Type u} [Field k] [CommRing A] [CommRing B] [CommRing S]
  [IsLocalRing A] [IsLocalRing B] [Algebra k A] [Algebra k B]
  [Algebra (A ⊗[k] B) S] [Module.Flat (A ⊗[k] B) S]

local notation "E" => (ModuleCat.extendScalars (algebraMap (A ⊗[k] B) S) :
  ModuleCat (A ⊗[k] B) ⥤ ModuleCat S)
local notation "box" => ModuleCat.exteriorTensorObj k
local notation "tor" => CategoryTheory.Tor

/-- The integer Euler characteristic of Tor for the two scalar-extended exterior products.
The residue tensor is kept with its full length, including any generic nonreducedness. -/
theorem finsum_length_extendScalars_exteriorTensor (M M' : ModuleCat.{u} A)
    (N N' : ModuleCat.{u} B)
    (hfA : ∀ n, IsFiniteLength A (((tor (ModuleCat.{u} A) n).obj M).obj M'))
    (hfB : ∀ n, IsFiniteLength B (((tor (ModuleCat.{u} B) n).obj N).obj N'))
    (hsA : {n : ℕ | ¬ IsZero (((tor (ModuleCat.{u} A) n).obj M).obj M')}.Finite)
    (hsB : {n : ℕ | ¬ IsZero (((tor (ModuleCat.{u} B) n).obj N).obj N')}.Finite)
    (hfres : Module.length S ((E).obj (box (ModuleCat.of A (IsLocalRing.ResidueField A))
      (ModuleCat.of B (IsLocalRing.ResidueField B)))) ≠ ⊤) :
    (∀ n : ℕ, IsFiniteLength S
      (((tor (ModuleCat.{u} S) n).obj ((E).obj (box M N))).obj ((E).obj (box M' N')))) ∧
    {n : ℕ | ¬ IsZero
      (((tor (ModuleCat.{u} S) n).obj ((E).obj (box M N))).obj ((E).obj (box M' N')))}.Finite ∧
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * ((Module.length S
      (((tor (ModuleCat.{u} S) n).obj ((E).obj (box M N))).obj ((E).obj (box M' N')))).toNat : ℤ)) =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        ((Module.length A (((tor (ModuleCat.{u} A) n).obj M).obj M')).toNat : ℤ)) *
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        ((Module.length B (((tor (ModuleCat.{u} B) n).obj N).obj N')).toNat : ℤ)) *
      ((Module.length S ((E).obj (box (ModuleCat.of A (IsLocalRing.ResidueField A))
        (ModuleCat.of B (IsLocalRing.ResidueField B))))).toNat : ℤ) := by
  let P := ProjectiveResolution.of M'
  let Q := ProjectiveResolution.of N'
  let K : CochainComplex (ModuleCat A) ℤ :=
    ((tensorLeft M).mapHomologicalComplex c).obj P.cochainComplex
  let L : CochainComplex (ModuleCat B) ℤ :=
    ((tensorLeft N).mapHomologicalComplex c).obj Q.cochainComplex
  let C := CochainComplex.exteriorTotalBaseChange (k := k) (S := S) K L
  have : K.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff K 0).2 fun p hp =>
    (tensorLeft M).map_isZero (P.cochainComplex.isZero_of_isStrictlyLE 0 p hp)
  have : L.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff L 0).2 fun q hq =>
    (tensorLeft N).map_isZero (Q.cochainComplex.isZero_of_isStrictlyLE 0 q hq)
  have : C.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff C 0).2 fun n hn =>
    (E).map_isZero (CochainComplex.isZero_of_isStrictlyLE
      ((CochainComplex.exteriorDouble (k := k) K L).total c) 0 n hn)
  let eK := tensorLeftCochainTorIso M M' P
  let eL := tensorLeftCochainTorIso N N' Q
  have hfK (p : ℤ) : IsFiniteLength A (K.homology p) := by
    by_cases hp : 0 < p
    · have : Subsingleton (K.homology p) := ModuleCat.subsingleton_of_isZero
        ((K.sc p).isZero_homology_of_isZero_X₂ (K.isZero_of_isStrictlyLE 0 p hp))
      exact IsFiniteLength.of_subsingleton
    · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat (le_of_not_gt hp)
      exact (eK n).symm.toLinearEquiv.isFiniteLength (hfA n)
  have hfL (q : ℤ) : IsFiniteLength B (L.homology q) := by
    by_cases hq : 0 < q
    · have : Subsingleton (L.homology q) := ModuleCat.subsingleton_of_isZero
        ((L.sc q).isZero_homology_of_isZero_X₂ (L.isZero_of_isStrictlyLE 0 q hq))
      exact IsFiniteLength.of_subsingleton
    · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat (le_of_not_gt hq)
      exact (eL n).symm.toLinearEquiv.isFiniteLength (hfB n)
  have hP (p : ℤ) : Module.Flat A (P.cochainComplex.X p) := by
    have : Module.Projective A (P.cochainComplex.X p) :=
      ModuleCat.projective_of_module_projective _
    infer_instance
  have hQ (q : ℤ) : Module.Flat B (Q.cochainComplex.X q) := by
    have : Module.Projective B (Q.cochainComplex.X q) :=
      ModuleCat.projective_of_module_projective _
    infer_instance
  obtain ⟨hCfin, hCsupp, h⟩ :=
    CochainComplex.finsum_length_exteriorTotalBaseChange (k := k) (S := S) K L 0 0
      (fun p hp => K.isZero_of_isStrictlyLE 0 p hp)
      (fun q hq => L.isZero_of_isStrictlyLE 0 q hq) hfK hfL
      (finite_homology_support_of_finite_tor K M M' eK hsA)
      (finite_homology_support_of_finite_tor L N N' eL hsB) hfres
  let eC := CochainComplex.exteriorTotalBaseChangeHomologyTorIso (k := k) (S := S)
    M N P.π' Q.π' hP hQ
  have hinj : Function.Injective (fun n : ℕ => -(n : ℤ)) :=
    fun _ _ h => Int.natCast_inj.mp (neg_injective h)
  refine ⟨fun n => (eC n).toLinearEquiv.isFiniteLength (hCfin (-(n : ℤ))), ?_, ?_⟩
  · exact (hCsupp.preimage hinj.injOn).subset fun n hn hz => hn (hz.of_iso (eC n).symm)
  · change (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * ((Module.length S (C.homology n)).toNat : ℤ)) = _ at h
    rw [finsum_homology_eq_tor C ((E).obj (box M N)) ((E).obj (box M' N')) eC,
      finsum_homology_eq_tor K M M' eK, finsum_homology_eq_tor L N N' eL] at h
    exact h

end ModuleCat.Tor

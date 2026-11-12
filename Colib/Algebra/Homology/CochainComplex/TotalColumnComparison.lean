/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.Filtration
import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Basic
import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.Convergence
import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.DoubleComplexSpectralSequences

/-!
# Columnwise comparisons for total complexes with finite diagonals

The graded piece of the first total filtration is the shifted column.
The identification uses the projection onto the original summand and
the sign of the original total differential.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.CechSpectral

set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace HomologicalComplex₂

variable {A : Type u} [Category.{v} A] [Abelian A]

local notation "c" => ComplexShape.up ℤ
local notation "Bicomplex(" A ")" => HomologicalComplex₂ A c c

variable (K : Bicomplex(A)) [K.HasTotal c]

private abbrev columnFiltrationInclusion (p n : ℤ) :=
  (K.totalFiltration₁.filtration.ι.app (op p)).f n

private abbrev columnFiltrationProjector (p n : ℤ) :=
  K.totalProjector (fun i (_ : ℤ) => p ≤ i) n

private abbrev columnFiltrationQuotient (p n : ℤ) :=
  (FilteredObject.grMapπ (FilteredObject.succHom p) K.totalFiltration₁).f n

private def totalColumnGrXIso (p q n : ℤ) (hn : p + q = n) :
    ((FilteredObject.gr p).obj K.totalFiltration₁).X n ≅ (K.X p).X q := by
  let F := K.totalFiltration₁
  let f := (F.filtration.diagram.map (FilteredObject.succHom p)).f n
  let a := columnFiltrationInclusion K p n
  let b := columnFiltrationInclusion K (p + 1) n
  let e := columnFiltrationProjector K p n
  let e' := columnFiltrationProjector K (p + 1) n
  let ι := K.ιTotal c p q n hn
  let π := totalSummandπ (K := K) p q n hn
  have ha : Subobject.mk a = imageSubobject e := K.mk_totalFiltration_ι_f _ _ _ p n
  have hb : Subobject.mk b = imageSubobject e' := K.mk_totalFiltration_ι_f _ _ _ (p + 1) n
  have hf : f ≫ a = b := by
    rw [← HomologicalComplex.comp_f, F.filtration.diagram_map_comp_ι_app]
  exact FilteredComplexSpectralSequence.gradedPieceXIso F p n ≪≫
    cokernelIsoOfProjectors e e' a b ha hb f hf ι π
      (K.totalProjector_idempotent _ _)
      (by rw [ι_totalProjector, ite_eq_left le_rfl])
      (ι_totalSummandπ _ _ _ _)
      (totalProjector_totalSummandπ_of_not _ _ _ _ _ (by omega))
      (totalProjector_add_totalSummandπ_ιTotal (K := K)
        (fun i (_ : ℤ) => i) p p q n hn rfl fun _ _ _ h => h)

@[reassoc]
private theorem columnFiltrationQuotient_comp_totalColumnGrXIso (p q n : ℤ)
    (hn : p + q = n) :
    columnFiltrationQuotient K p n ≫ (totalColumnGrXIso K p q n hn).hom =
      columnFiltrationInclusion K p n ≫ totalSummandπ (K := K) p q n hn := by
  unfold totalColumnGrXIso
  rw [Iso.trans_hom, ← Category.assoc,
    FilteredComplexSpectralSequence.gradedPieceπ_f_gradedPieceXIso_hom]
  apply cokernelIsoOfProjectors_π

private theorem columnFiltrationProjector_d_totalSummandπ (p q n m : ℤ)
    (hn : p + q = n) (hm : p + (q + 1) = m) :
    columnFiltrationProjector K p n ≫ (K.total c).d n m ≫
      totalSummandπ (K := K) p (q + 1) m hm =
      totalSummandπ (K := K) p q n hn ≫ (p.negOnePow • (K.X p).d q (q + 1)) := by
  subst n
  obtain rfl : m = p + q + 1 := by omega
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  have hij' : i + j = p + q := hij
  rw [ι_totalProjector_assoc]
  by_cases hi : i = p
  · subst i
    obtain rfl : j = q := by omega
    rw [ite_eq_left le_rfl, ι_total_d_assoc, Preadditive.add_comp, Category.assoc,
      ι_totalSummandπ_of_ne _ _ _ _ _ _ _ (by omega), comp_zero, zero_add,
      Linear.units_smul_comp, Category.assoc, ι_totalSummandπ, Category.comp_id,
      ι_totalSummandπ_assoc]
  · rw [ι_totalSummandπ_of_ne_assoc _ _ _ _ _ _ hij' hi, zero_comp]
    split_ifs with hp
    · rw [ι_total_d_assoc, Preadditive.add_comp, Category.assoc, Linear.units_smul_comp,
        Category.assoc, ι_totalSummandπ_of_ne _ _ _ _ _ _ _ (by omega),
        ι_totalSummandπ_of_ne _ _ _ _ _ _ _ hi, comp_zero, comp_zero, smul_zero, add_zero]
    · exact zero_comp

private theorem columnFiltrationInclusion_d_totalSummandπ (p q n m : ℤ)
    (hn : p + q = n) (hm : p + (q + 1) = m) :
    columnFiltrationInclusion K p n ≫ (K.total c).d n m ≫
      totalSummandπ (K := K) p (q + 1) m hm =
      columnFiltrationInclusion K p n ≫ totalSummandπ (K := K) p q n hn ≫
        (p.negOnePow • (K.X p).d q (q + 1)) := by
  let a := columnFiltrationInclusion K p n
  let e := columnFiltrationProjector K p n
  have ha : Subobject.mk a = imageSubobject e := K.mk_totalFiltration_ι_f _ _ _ p n
  have he : a ≫ e = a :=
    comp_idempotent_of_mk_eq e (K.totalProjector_idempotent _ _) a ha
  change a ≫ (K.total c).d n m ≫ totalSummandπ p (q + 1) m hm = _
  calc
    _ = a ≫ e ≫ (K.total c).d n m ≫ totalSummandπ p (q + 1) m hm := by
      rw [← Category.assoc a e, he]
    _ = _ := congrArg (fun g => a ≫ g)
      (columnFiltrationProjector_d_totalSummandπ K p q n m hn hm)

/-- The first graded piece in column `p` is that column shifted by `-p`. -/
def totalColumnGrIso (p : ℤ) :
    (FilteredObject.gr p).obj K.totalFiltration₁ ≅ (K.X p)⟦-p⟧ := by
  let q (n : ℤ) := n + -p
  let e (n : ℤ) := totalColumnGrXIso K p (q n) n (by dsimp [q]; omega)
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro n m hnm
  change n + 1 = m at hnm
  have hq : q n + 1 = q m := by dsimp [q]; omega
  let a := K.totalFiltration₁.filtration.ι.app (op p)
  let b := FilteredObject.grMapπ (FilteredObject.succHom p) K.totalFiltration₁
  have hb : Epi (b.f n) := by
    change Epi ((HomologicalComplex.eval A c n).map b)
    infer_instance
  apply (cancel_epi (b.f n)).mp
  change b.f n ≫ (e n).hom ≫ ((K.X p)⟦-p⟧).d n m =
    b.f n ≫ ((FilteredObject.gr p).obj K.totalFiltration₁).d n m ≫ (e m).hom
  rw [columnFiltrationQuotient_comp_totalColumnGrXIso_assoc,
    CochainComplex.shiftFunctor_obj_d', Int.negOnePow_neg,
    HomologicalComplex.Hom.comm_assoc, columnFiltrationQuotient_comp_totalColumnGrXIso]
  change _ = (K.totalFiltration₁.filtration.obj (op p)).d n m ≫
    a.f m ≫ totalSummandπ p (q m) m _
  rw [← HomologicalComplex.Hom.comm_assoc a]
  change columnFiltrationInclusion K p n ≫ totalSummandπ p (q n) n _ ≫
      (p.negOnePow • (K.X p).d (q n) (q m)) =
    columnFiltrationInclusion K p n ≫ (K.total c).d n m ≫ totalSummandπ p (q m) m _
  have hprojection := columnFiltrationInclusion_d_totalSummandπ K p (q n) n m
    (by dsimp [q]; omega) (by dsimp [q]; omega)
  let q' := q n + 1
  change q' = q m at hq
  have hn : p + q n = n := by dsimp [q]; omega
  let property (j : ℤ) : Prop := ∀ hj : p + j = m,
    columnFiltrationInclusion K p n ≫ totalSummandπ p (q n) n hn ≫
        (p.negOnePow • (K.X p).d (q n) j) =
      columnFiltrationInclusion K p n ≫ (K.total c).d n m ≫ totalSummandπ p j m hj
  have hh : property q' := fun _ => hprojection.symm
  exact (hq ▸ hh) (by dsimp [q]; omega)

private theorem totalColumnGrIso_hom_f (p n : ℤ) :
    (totalColumnGrIso K p).hom.f n =
      (totalColumnGrXIso K p (n + -p) n (by omega)).hom := by
  unfold totalColumnGrIso
  rfl

variable {K} {L : Bicomplex(A)} [L.HasTotal c]

private abbrev columnFiltrationMap (f : K ⟶ L) : K.totalFiltration₁ ⟶ L.totalFiltration₁ :=
  totalFiltrationMap (fun i (_ : ℤ) => i) (fun _ _ => by omega) (fun _ _ => le_rfl) f

private theorem total_map_f_totalSummandπ (f : K ⟶ L) (p q n : ℤ) (hn : p + q = n) :
    (HomologicalComplex₂.total.map f c).f n ≫ totalSummandπ (K := L) p q n hn =
      totalSummandπ (K := K) p q n hn ≫ (f.f p).f q := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  have hij' : i + j = n := hij
  rw [ιTotal_map_assoc]
  by_cases hi : i = p
  · subst i
    obtain rfl : j = q := by omega
    simp only [ι_totalSummandπ, Category.comp_id, ι_totalSummandπ_assoc]
  · rw [ι_totalSummandπ_of_ne _ _ _ _ _ _ hij' hi, comp_zero,
      ι_totalSummandπ_of_ne_assoc _ _ _ _ _ _ hij' hi, zero_comp]

private theorem totalColumnGrIso_naturality (f : K ⟶ L) (p : ℤ) :
    (FilteredObject.gr p).map (columnFiltrationMap f) ≫ (totalColumnGrIso L p).hom =
      (totalColumnGrIso K p).hom ≫ (f.f p)⟦-p⟧' := by
  apply FilteredObject.grMap_hom_ext (FilteredObject.succHom p)
  rw [FilteredObject.grMapπ_map_assoc]
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, totalColumnGrIso_hom_f,
    CochainComplex.shiftFunctor_map_f']
  let F := columnFiltrationMap f
  let q := n + -p
  have hn : p + q = n := by dsimp [q]; omega
  change (F.natTrans.app (op p)).f n ≫
      (columnFiltrationQuotient L p n ≫ (totalColumnGrXIso L p q n hn).hom) =
    columnFiltrationQuotient K p n ≫ (totalColumnGrXIso K p q n hn).hom ≫ (f.f p).f q
  rw [columnFiltrationQuotient_comp_totalColumnGrXIso]
  change (totalFiltrationStepMap (fun i (_ : ℤ) => i) (fun _ _ => by omega)
      (fun _ _ => le_rfl) f p).f n ≫ (imageSubobject (L.columnFiltrationProjector p n)).arrow ≫
      totalSummandπ p q n hn = _
  rw [totalFiltrationStepMap_f_arrow_assoc, total_map_f_totalSummandπ,
    columnFiltrationQuotient_comp_totalColumnGrXIso_assoc]
  rfl

/-- A columnwise quasi-isomorphism induces a quasi-isomorphism of total
complexes when both bicomplexes have finite diagonals. -/
theorem quasiIso_totalMap_of_columnwise (f : K ⟶ L)
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ |
      pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite)
    (hL : ∀ n : ℤ, {pq : ℤ × ℤ |
      pq.1 + pq.2 = n ∧ ¬ IsZero ((L.X pq.1).X pq.2)}.Finite)
    (hf : ∀ p : ℤ, QuasiIso (f.f p)) : QuasiIso (HomologicalComplex₂.total.map f c) := by
  apply CochainComplex.quasiIso_hom_of_filteredQuasiIso (columnFiltrationMap f) _
    (K.isDegreewiseFinite_totalFiltration₁ hK) (L.isDegreewiseFinite_totalFiltration₁ hL)
  intro p
  have hi := (CochainComplex.quasiIso_shift_iff (f.f p) (-p)).2 (hf p)
  have hc : QuasiIso ((FilteredObject.gr p).map (columnFiltrationMap f) ≫
      (totalColumnGrIso L p).hom) := by
    rw [totalColumnGrIso_naturality]
    exact quasiIso_comp _ _
  exact quasiIso_of_comp_right _ (totalColumnGrIso L p).hom

/-- Totalization commutes with the actual signed symmetry on a map of
double complexes. -/
theorem totalFlipIso_hom_naturality_map [K.flip.HasTotal c] [L.flip.HasTotal c] (f : K ⟶ L) :
    let f' : K.flip ⟶ L.flip := (flipFunctor A c c).map f
    HomologicalComplex₂.total.map f' c ≫ (totalFlipIso L c).hom =
      (totalFlipIso K c).hom ≫ HomologicalComplex₂.total.map f c := by
  let f' : K.flip ⟶ L.flip := (flipFunctor A c c).map f
  change total.map f' c ≫ (totalFlipIso L c).hom =
    (totalFlipIso K c).hom ≫ total.map f c
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex₂.total.hom_ext
  intro q p hpq
  rw [ιTotal_map_assoc, ιTotal_totalFlipIso_f_hom, ιTotal_totalFlipIso_f_hom_assoc]
  change (f.f p).f q ≫ (ComplexShape.σ c c c p q • L.ιTotal c p q n _) =
    (ComplexShape.σ c c c p q • K.ιTotal c p q n _) ≫ (total.map f c).f n
  rw [Linear.comp_units_smul, Linear.units_smul_comp, ιTotal_map]

end HomologicalComplex₂

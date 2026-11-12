/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeTensorInf
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FiniteFlatZeros

/-!
# The actual product ideal of a tensor-product section

The zero ideal of `a tensor b` is the product of the two native zero ideals.
This is not the ideal intersection and needs no disjointness, reducedness or
regularity hypothesis. Local generator coordinates prove the equality on a full
affine cover. All scheme structures and multiplicities are retained.

This supplies the geometric input to the separate finite-flat whole-cycle
additivity theorem. It does not assert unconditional cycle additivity.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Divisors TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {X : Scheme.{u}} (M N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- The full zero ideal of the native tensor section is the product ideal,
including all nilpotents and coincident components. -/
theorem zeroScheme_tensorSection_eq_mul (a : Γ(M, ⊤)) (b : Γ(N, ⊤)) :
    zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b) =
      zeroScheme X M a * zeroScheme X N b := by
  classical
  have hlocal (x : X) : ∃ U : X.affineOpens, x ∈ U.1 ∧
      (zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b)).ideal U =
        (zeroScheme X M a * zeroScheme X N b).ideal U := by
    obtain ⟨U, hx, -, ⟨g⟩, ⟨w⟩⟩ := exists_affineOpens_generator_pair M N x ⊤ trivial
    obtain ⟨α, ha⟩ := exists_coord_of_generator M a g
    obtain ⟨β, hb⟩ := exists_coord_of_generator N b w
    refine ⟨U, hx, ?_⟩
    rw [zeroScheme_ideal_tensorSection_of_generators M N a b U g w α β ha hb,
      IdealSheafData.ideal_mul, Pi.mul_apply,
      zeroScheme_ideal_eq_span_singleton_of_bijective_smul X M a U
        (generatorVal M g) (bijective_smul_generator M g) α ha,
      zeroScheme_ideal_eq_span_singleton_of_bijective_smul X N b U
        (generatorVal N w) (bijective_smul_generator N w) β hb,
      Ideal.span_singleton_mul_span_singleton]
  choose U hx hU using hlocal
  exact IdealSheafData.ext_of_iSup_eq_top U
    (eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩) hU

/-- The exact three-factor zero ideal, in the tensor order used by the pencil start. -/
theorem zeroScheme_tensorSection_triple (P : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property P]
    (a : Γ(M, ⊤)) (b : Γ(N, ⊤)) (c : Γ(P, ⊤)) :
    zeroScheme X (tensorModules (tensorModules M N) P)
      (tensorSection (tensorModules M N) P ⊤ (tensorSection M N ⊤ a b) c) =
        (zeroScheme X M a * zeroScheme X N b) * zeroScheme X P c := by
  rw [zeroScheme_tensorSection_eq_mul, zeroScheme_tensorSection_eq_mul]

/-- The polynomial pencil start is the actual graph ideal times both pole ideals. -/
theorem zeroScheme_graph_tensor_poles (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (b : Γ(M, ⊤)) (d : Γ(N, ⊤)) :
    zeroScheme X (tensorModules (tensorModules (divisorSheaf D) M) N)
      (tensorSection (tensorModules (divisorSheaf D) M) N ⊤
        (tensorSection (divisorSheaf D) M ⊤ (divisorSheafGlobalSection D) b) d) =
          (D * zeroScheme X M b) * zeroScheme X N d := by
  rw [zeroScheme_tensorSection_triple, zeroScheme_canonicalSection]

/-- Whole support containment is preserved under actual tensor products. -/
theorem tensorSection_whole_support_subset {C : Scheme.{u}} (j : C ⟶ X)
    (a : Γ(M, ⊤)) (b : Γ(N, ⊤))
    (ha : Set.range (zeroScheme X M a).subschemeι ⊆ Set.range j)
    (hb : Set.range (zeroScheme X N b).subschemeι ⊆ Set.range j) :
    Set.range (zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b)).subschemeι ⊆
      Set.range j := by
  rw [zeroScheme_tensorSection_eq_mul, IdealSheafData.range_subschemeι,
    IdealSheafData.support_mul]
  rw [IdealSheafData.range_subschemeι] at ha hb
  exact Set.union_subset ha hb

/-- The tensor-product zero scheme is finite and relative Cartier on the original
retained open, derived from the two actual whole supports and properness. -/
theorem finite_relativeCartier_tensorSection {S C : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsAffine S] (j : C ⟶ X) [IsOpenImmersion j]
    [C.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ f)]
    (a : Γ(M, ⊤)) (b : Γ(N, ⊤))
    (ha : Set.range (zeroScheme X M a).subschemeι ⊆ Set.range j)
    (hb : Set.range (zeroScheme X N b).subschemeι ⊆ Set.range j) :
    IsFinite ((zeroScheme C ((Modules.pullback j).obj (tensorModules M N))
        (pullbackGlobalSections j _ (tensorSection M N ⊤ a b))).subschemeι ≫ (j ≫ f)) ∧
      Stacks.Divisors.IsRelativeEffectiveCartierDivisor (j ≫ f)
        (zeroScheme C ((Modules.pullback j).obj (tensorModules M N))
          (pullbackGlobalSections j _ (tensorSection M N ⊤ a b))) :=
  finite_relativeCartier_zeroScheme_on_open_of_proper f j _ _
    (tensorSection_whole_support_subset M N j a b ha hb)

end AlgebraicGeometry.Scheme.RelativeCurvePencil

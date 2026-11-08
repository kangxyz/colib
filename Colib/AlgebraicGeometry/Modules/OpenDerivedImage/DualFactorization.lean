/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Closure
public import Colib.Algebra.Homology.HomotopyPullback.QuasiIso

/-!
# Strict incoming factorization through two actual homotopy pullbacks

Given the geometric roof input between global perfect models, two literal homotopy pullbacks
turn the genuine common-denominator homotopies into strict chain-map equations. The resulting
maps are degreewise split epimorphisms, and their actual categorical kernels belong to the
source and target. This is an incoming, dual factorization, not outgoing strict App2.

Adapted from Quillen's `OpenDerivedImage/DualFactorization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules]

local notation "R" => Functor.mapHomologicalComplex (restrictFunctor j) (ComplexShape.up ℤ)

private theorem isPerfectComplex_kernel_of_epi {K L : CochainComplex X.Modules ℤ}
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K)
    (hL : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) L) (f : K ⟶ L) [Epi f] :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace) (kernel f) := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact :=
    { exact := S.exact_of_f_is_kernel (kernelIsKernel f)
      mono_f := inferInstance
      epi_g := inferInstance }
  exact RingedSpace.isPerfectComplex_X₁_of_shortExact X.toRingedSpace hS hK hL

/-- Original dual App2 data with both literal triangles, actual componentwise
split epis and genuine kernel membership in the corresponding source/target.
The input roof property concerns only globally perfect models. -/
theorem exists_dual_factorization (hroof : HasDerivedRoofs j)
    (P : CochainComplex X.Modules ℤ)
    (hP : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) P)
    (B B' : CochainComplex U.Modules ℤ)
    (hB' : complexObjects j B') (w : (R).obj P ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : CochainComplex X.Modules ℤ) (D : CochainComplex U.Modules ℤ)
      (c : C ⟶ P) (d : D ⟶ B) (u : (R).obj C ⟶ D) (v : B' ⟶ D),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) C ∧
      complexObjects j D ∧ QuasiIso u ∧ QuasiIso v ∧
      u ≫ d = (R).map c ≫ w ∧ v ≫ d = b ∧
      (∀ i, IsSplitEpi (c.f i)) ∧ (∀ i, IsSplitEpi (d.f i)) ∧
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) (kernel c) ∧
      complexObjects j (kernel d) := by
  obtain ⟨A, M, N, a, p, t, s, q, hA, hM, hN, hp, ht, hs, ⟨H₁⟩, ⟨H₂⟩⟩ :=
    exists_homotopy_roof j hroof P hP B B' hB' w b
  let C := homotopyPullback a (𝟙 P)
  let cA : C ⟶ A := homotopyPullbackFst a (𝟙 P)
  let c : C ⟶ P := homotopyPullbackSnd a (𝟙 P)
  have hcA : QuasiIso cA := quasiIso_homotopyPullbackFst a (𝟙 P)
  have hC : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) C :=
    (RingedSpace.isPerfectComplex_iff_of_quasiIso cA hcA).2 hA
  let D := homotopyPullback q s
  let d : D ⟶ B := homotopyPullbackSnd q s
  have Hc : Homotopy ((R).map cA ≫ (R).map a) ((R).map c) := by
    simpa only [cA, c, C, Functor.map_comp, Functor.map_id, Category.comp_id] using
      (Scheme.Modules.restrictFunctor j).mapHomotopy (homotopyPullbackProjectionHomotopy a (𝟙 P))
  have H : Homotopy (((R).map cA ≫ p) ≫ q) (((R).map c ≫ w) ≫ s) := by
    have Hpre : Homotopy (((R).map cA ≫ p) ≫ q)
        (((R).map cA ≫ (R).map a) ≫ w ≫ s) := by
      simpa only [Category.assoc] using H₁.compLeft ((R).map cA)
    have Hpost : Homotopy (((R).map cA ≫ (R).map a) ≫ w ≫ s)
        (((R).map c ≫ w) ≫ s) := by
      simpa only [Category.assoc] using Hc.compRight (w ≫ s)
    exact Hpre.trans Hpost
  let u : (R).obj C ⟶ D := homotopyPullbackLift q s
    ((R).map cA ≫ p) ((R).map c ≫ w) H
  let v : B' ⟶ D := homotopyPullbackLift q s t b H₂
  have hu : QuasiIso u := quasiIso_homotopyPullbackLift q s
    ((R).map cA ≫ p) ((R).map c ≫ w) H
  have hv : QuasiIso v := quasiIso_homotopyPullbackLift q s t b H₂
  have hD : complexObjects j D := ⟨C, hC, ⟨asIso ((DerivedCategory.Q (C := U.Modules)).map u)⟩⟩
  have hB : complexObjects j B := ⟨P, hP, ⟨asIso ((DerivedCategory.Q (C := U.Modules)).map w)⟩⟩
  have hc (i : ℤ) : IsSplitEpi (c.f i) :=
    IsSplitEpi.mk' (homotopyPullbackSndSplitEpi a (𝟙 P) i)
  have hd (i : ℤ) : IsSplitEpi (d.f i) :=
    IsSplitEpi.mk' (homotopyPullbackSndSplitEpi q s i)
  have : Epi c := HomologicalComplex.epi_of_epi_f c (fun i => by have := hc i; infer_instance)
  have : Epi d := HomologicalComplex.epi_of_epi_f d (fun i => by have := hd i; infer_instance)
  let S := ShortComplex.mk (kernel.ι d) d (kernel.condition d)
  have hS : S.ShortExact := {
    exact := S.exact_of_f_is_kernel (kernelIsKernel d)
    mono_f := inferInstance
    epi_g := inferInstance }
  exact ⟨C, D, c, d, u, v, hC, hD, hu, hv,
    homotopyPullbackLift_snd q s ((R).map cA ≫ p) ((R).map c ≫ w) H,
    homotopyPullbackLift_snd q s t b H₂, hc, hd,
    isPerfectComplex_kernel_of_epi hC hP c,
    complexObjects_kernel_of_shortExact j hroof hS hD hB⟩

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

attribute [colib_tag "COL-0312",
  colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/OpenDerivedImage/DualFactorization.lean"
    "adaptation"
    "Two pullbacks give strict incoming equations and actual kernels from global-model roofs"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.exists_dual_factorization

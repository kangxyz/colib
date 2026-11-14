/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Units.KummerRootUnit
public import Colib.AlgebraicGeometry.Sites.Smooth.Units.EtaleSheaf
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Local extraction of roots on the actual smooth étale site -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [instance] CategoryTheory.sheafIsAbelian

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.Kummer

/-- The literal power map is locally surjective on the original smooth étale site. -/
theorem power_isLocallySurjective (S : Scheme.{u}) (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(S, ⊤))) :
    Presheaf.IsLocallySurjective (etaleTopology S)
      (n • 𝟙 (unitsPresheaf S)) := by
  refine ⟨fun {T} s => ?_⟩
  let v : Γ(T.left, ⊤)ˣ := Additive.toMul s
  have hT : IsUnit (n : Γ(T.left, ⊤)) := by
    simpa only [map_natCast] using hunit.map T.hom.appTop.hom
  let W : PreZeroHypercover T := {
    I₀ := Unit
    X _ := rootObject T v n hn hT
    f _ := rootObjectMap T v n hn hT }
  have hW : W.presieve₀ ∈ etalePrecoverage S T := rootObject_cover T v n hn hT
  have hcover : Sieve.generate W.presieve₀ ∈ etaleTopology S T :=
    Precoverage.generate_mem_toGrothendieck hW
  apply (etaleTopology S).superset_covering ?_ hcover
  apply (Sieve.generate_le_iff _ _).2
  rintro V g ⟨i⟩
  refine ⟨Additive.ofMul (rootOnCover v n hn), ?_⟩
  change n • (Additive.ofMul (rootOnCover v n hn) :
    Additive Γ(rootScheme v n, ⊤)ˣ) =
    Additive.ofMul (Units.map (rootProjection v n).appTop.hom.toMonoidHom v)
  rw [← ofMul_pow, rootOnCover_pow]

/-- Local extraction of roots also holds in the original large coefficient universe. -/
theorem largePower_isLocallySurjective (S : Scheme.{u}) (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(S, ⊤))) :
    Presheaf.IsLocallySurjective (etaleTopology S)
      (n • 𝟙 (largeUnitsPresheaf S)) := by
  have hlow := power_isLocallySurjective S n hn hunit
  refine ⟨fun {T} s => ?_⟩
  have hc := hlow.imageSieve_mem s.down
  apply (etaleTopology S).superset_covering ?_ hc
  intro V f hf
  obtain ⟨b, hb⟩ := hf
  refine ⟨ULift.up b, ?_⟩
  change ULift.up ((n • 𝟙 (unitsPresheaf S)).app (op V) b) =
    ULift.up ((unitsPresheaf S).map f.op s.down)
  rw [hb]

/-- Multiplication by the invertible degree is epi on the actual large étale units sheaf. -/
@[colib_tag "COL-1233",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/EtaleCohomology/KummerTheory/RootExtraction.lean:54-101"
    "ingredient" "Finite etale root algebra and its actual root unit",
  colib_ref "stacks" "Tag 03PL" "specialization"
    "Kummer root extraction on the original smooth etale site"]
theorem largeUnitsEtaleSheaf_nsmul_epi (S : Scheme.{u}) (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(S, ⊤))) :
    Epi (n • 𝟙 (largeUnitsEtaleSheaf S)) := by
  let : Sheaf.IsLocallySurjective (n • 𝟙 (largeUnitsEtaleSheaf S)) :=
    largePower_isLocallySurjective S n hn hunit
  exact Sheaf.epi_of_isLocallySurjective _

/-- The actual large smooth étale Kummer sequence, with the literal power-map kernel. -/
def kummerSequence (S : Scheme.{u})
    [HasSheafify (etaleTopology S) AddCommGrpCat.{u + 1}] (n : ℕ) :
    ShortComplex (Sheaf (etaleTopology S) AddCommGrpCat.{u + 1}) :=
  ShortComplex.kernelSequence (n • 𝟙 (largeUnitsEtaleSheaf S))

/-- The actual smooth étale Kummer sequence is short exact. -/
@[colib_tag "COL-1233",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/Algebra/Homology/ShortComplex/Exact.lean:881-882"
    "specialization" "Native kernel sequence exactness plus the proved power-map epimorphism"]
theorem kummerSequence_shortExact (S : Scheme.{u})
    [HasSheafify (etaleTopology S) AddCommGrpCat.{u + 1}] (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(S, ⊤))) : (kummerSequence S n).ShortExact := by
  unfold kummerSequence
  exact .mk' (ShortComplex.kernelSequence_exact _) inferInstance
    (largeUnitsEtaleSheaf_nsmul_epi S n hn hunit)

end AlgebraicGeometry.Scheme.SmoothSite.Kummer

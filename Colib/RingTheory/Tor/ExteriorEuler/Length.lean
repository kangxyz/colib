/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Tor.ExteriorEuler.ExteriorTensor
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# Length of a base-changed exterior tensor product

For finite-length modules over two local algebras of a field, the length of their exterior
tensor product after flat base change is the product of their lengths and the length of the
base-changed tensor of the two residue fields. The latter length retains the multiplicity of
the residual tensor algebra, including at a nonreduced generic point.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

universe u

variable {A S : Type u} [CommRing A] [CommRing S] [IsLocalRing A]

private theorem length_eq_add_of_shortExact {R : Type u} [CommRing R]
    {C : ShortComplex (ModuleCat.{u} R)} (hC : C.ShortExact) :
    Module.length R C.X₂ = Module.length R C.X₁ + Module.length R C.X₃ :=
  Module.length_eq_add_of_exact C.f.hom C.g.hom hC.moduleCat_injective_f
    hC.moduleCat_surjective_g ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact C).mp
      hC.exact)

private theorem length_obj_eq_mul_of_exact (F : ModuleCat.{u} A ⥤ ModuleCat.{u} S)
    [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    (M : Type u) [AddCommGroup M] [Module A M]
    (hM : IsFiniteLength A M) :
    Module.length S (F.obj (ModuleCat.of A M)) =
      Module.length A M *
        Module.length S (F.obj (ModuleCat.of A (IsLocalRing.ResidueField A))) := by
  induction hM with
  | @of_subsingleton M _ _ hM =>
    have hzero := F.map_isZero (X := ModuleCat.of A M)
      (ModuleCat.isZero_iff_subsingleton.mpr hM)
    have := ModuleCat.subsingleton_of_isZero hzero
    simp
  | @of_simple_quotient M _ _ N _ _ ih =>
    let C := ShortComplex.moduleCatMk N.subtype N.mkQ
      (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero
    have hC : C.ShortExact := ModuleCat.shortComplex_shortExact C
      (LinearMap.exact_subtype_mkQ N) N.subtype_injective N.mkQ_surjective
    have hFC := hC.map_of_exact F
    have hlen := length_eq_add_of_shortExact hFC
    change Module.length S (F.obj (ModuleCat.of A M)) =
      Module.length S (F.obj (ModuleCat.of A N)) +
        Module.length S (F.obj (ModuleCat.of A (M ⧸ N))) at hlen
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
      (inferInstance : IsSimpleModule A (M ⧸ N))
    rw [IsLocalRing.eq_maximalIdeal hI] at e
    have hres : Module.length S (F.obj (ModuleCat.of A (M ⧸ N))) =
        Module.length S (F.obj (ModuleCat.of A (IsLocalRing.ResidueField A))) :=
      (F.mapIso e.toModuleIso).toLinearEquiv.length_eq
    have hA := length_eq_add_of_shortExact hC
    change Module.length A M = Module.length A N + Module.length A (M ⧸ N) at hA
    rw [hlen, ih, hres, hA, Module.length_eq_one A (M ⧸ N), add_mul, one_mul]

variable {k B : Type u} [Field k] [CommRing B] [IsLocalRing B] [Algebra k A] [Algebra k B]
  [Algebra (A ⊗[k] B) S] [Module.Flat (A ⊗[k] B) S]

/-- The product of the two input lengths and the base-changed residue tensor length is the
length of the actual base-changed exterior tensor. The equality is in `ℕ∞`. -/
theorem length_extendScalars_exteriorTensor (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)
    (hM : IsFiniteLength A M) (hN : IsFiniteLength B N) :
    let E := ModuleCat.extendScalars (algebraMap (A ⊗[k] B) S)
    Module.length S (E.obj (exteriorTensorObj k M N)) =
      Module.length A M * Module.length B N *
        Module.length S (E.obj (exteriorTensorObj k
          (ModuleCat.of A (IsLocalRing.ResidueField A))
          (ModuleCat.of B (IsLocalRing.ResidueField B)))) := by
  dsimp only
  let E := ModuleCat.extendScalars (algebraMap (A ⊗[k] B) S)
  let : Limits.PreservesFiniteLimits E := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (A ⊗[k] B) S))
  let F := (exteriorTensor (k := k) (A := A)).flip.obj N ⋙ E
  let G := (exteriorTensor (k := k) (B := B)).obj (ModuleCat.of A (IsLocalRing.ResidueField A)) ⋙ E
  let := Functor.preservesFiniteLimits_of_preservesHomology
    ((exteriorTensor (k := k) (A := A)).flip.obj N)
  let := Functor.preservesFiniteColimits_of_preservesHomology
    ((exteriorTensor (k := k) (A := A)).flip.obj N)
  let := Functor.preservesFiniteLimits_of_preservesHomology
    ((exteriorTensor (k := k) (B := B)).obj (ModuleCat.of A (IsLocalRing.ResidueField A)))
  let := Functor.preservesFiniteColimits_of_preservesHomology
    ((exteriorTensor (k := k) (B := B)).obj (ModuleCat.of A (IsLocalRing.ResidueField A)))
  calc
    _ = Module.length A M *
        Module.length S (G.obj N) :=
      length_obj_eq_mul_of_exact F M hM
    _ = _ := by
      change Module.length A M * Module.length S (G.obj N) =
        Module.length A M * Module.length B N *
          Module.length S (G.obj (ModuleCat.of B (IsLocalRing.ResidueField B)))
      rw [length_obj_eq_mul_of_exact G N hN, mul_assoc]

end ModuleCat

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Exactness
public import Colib.CategoryTheory.Limits.ReflectiveColimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
Implementation adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Sheaf/UnderlyingExactness.lean`,
blob `1d78ab10287d5fa4845025793428d10e421c9a92`.

# Exactness of the ordinary underlying sheaf functor

Forgetting transfers preserves ordinary sheaf colimits because genuine
transfer sheafification commutes with ordinary Nisnevich sheafification.
Combined with limit preservation this proves exactness and gives the canonical
kernel and cokernel comparisons. Ordinary sheaf cokernels are not asserted
to be objectwise cokernels of sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w w'

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]
/-- Forgetting transfers preserves sheaf colimits, including sheaf cokernels. -/
instance toSheaf_preservesColimitsOfShape (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J AddCommGrpCat.{u + 1}] :
    PreservesColimitsOfShape J (toSheaf.{u + 1} k) := by
  have : PreservesColimitsOfShape J
      (PresheafWithTransfers.nisnevichSheafify k ⋙ toSheaf.{u + 1} k) :=
    preservesColimitsOfShape_of_natIso
      (PresheafWithTransfers.nisnevichSheafificationUnderlyingIso k)
  exact preservesColimitsOfShape_of_reflector
    (PresheafWithTransfers.nisnevichSheafify k) (forget k) (toSheaf k)
    (asIso (PresheafWithTransfers.nisnevichSheafificationAdjunction k).counit)

instance toSheaf_preservesFiniteColimits : PreservesFiniteColimits (toSheaf.{u + 1} k) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- The underlying ordinary sheaf of a transfer kernel is the ordinary kernel. -/
def underlyingKernelIso {F G : SheafWithTransfers.{u + 1} k} (f : F ⟶ G) :
    (toSheaf k).obj (kernel f) ≅ kernel ((toSheaf k).map f) :=
  PreservesKernel.iso (toSheaf k) f

/-- The underlying ordinary sheaf of a transfer cokernel is the ordinary sheaf cokernel. -/
def underlyingCokernelIso {F G : SheafWithTransfers.{u + 1} k} (f : F ⟶ G) :
    (toSheaf k).obj (cokernel f) ≅ cokernel ((toSheaf k).map f) :=
  PreservesCokernel.iso (toSheaf k) f

@[reassoc (attr := simp)]
theorem underlyingKernelIso_hom_ι {F G : SheafWithTransfers.{u + 1} k} (f : F ⟶ G) :
    (underlyingKernelIso k f).hom ≫ kernel.ι ((toSheaf k).map f) =
      (toSheaf k).map (kernel.ι f) :=
  kernelComparison_comp_ι f (toSheaf k)

@[reassoc (attr := simp)]
theorem underlyingCokernelIso_π_hom {F G : SheafWithTransfers.{u + 1} k} (f : F ⟶ G) :
    (toSheaf k).map (cokernel.π f) ≫ (underlyingCokernelIso k f).hom =
      cokernel.π ((toSheaf k).map f) := by
  simp [underlyingCokernelIso]

/-- Exactness of actual transfer sheaves is preserved and detected on ordinary sheaves. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Sheaf/UnderlyingExactness.lean:69-71"
  "adaptation" "Actual native reflection and ordinary sheaf comparison maps"]
theorem exact_toSheaf_iff (S : ShortComplex (SheafWithTransfers.{u + 1} k)) :
    (S.map (toSheaf k)).Exact ↔ S.Exact :=
  S.exact_map_iff_of_faithful (toSheaf k)

/-- Every short exact sequence of transfer sheaves is ordinary-sheaf short exact. -/
theorem shortExact_toSheaf {S : ShortComplex (SheafWithTransfers.{u + 1} k)}
    (hS : S.ShortExact) : (S.map (toSheaf k)).ShortExact :=
  hS.map_of_exact (toSheaf k)

end AlgebraicGeometry.SheafWithTransfers

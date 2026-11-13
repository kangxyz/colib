/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteDiagonalIntegration
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.DoubleSimplexSwap
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TotalComparison

/-!
# The tricomplex of iterated singularization

Finite diagonal support identifies successive singular totalizations with the
native tricomplex totalization. The comparison sends each summand to the
original inner inclusion followed by the outer inclusion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "c" => ComplexShape.up ℤ
local notation "S" => singularCoChains k

/-- The coefficient degree followed by the two original singular cochain degrees. -/
abbrev iteratedSingularTricomplex (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ) :
    HomologicalComplex₃ (PresheafWithTransfers.{v} k) c c c :=
  let G : PresheafWithTransfers.{v} k ⥤ CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
    singularCoChains k
  HomologicalComplex₂.TotalMap.mapBicomplex G ((singularBicomplexFunctor k).obj K)

/-- Compare the total of the last two indices first with successive singular totalization. -/
@[no_expose]
def iteratedSingularTotalFromColumns (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] :
    (iteratedSingularTricomplex K).total₂₃ c c ≅
      (singularTotalFunctor k).obj ((singularTotalFunctor k).obj K) := by
  let G : PresheafWithTransfers.{v} k ⥤ CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
    singularCoChains k
  let B := (singularBicomplexFunctor k).obj K
  change (iteratedSingularTricomplex K).total₂₃ c c ≅
    HomologicalComplex₂.total ((G.mapHomologicalComplex c).obj (B.total c)) c
  exact HomologicalComplex₂.TotalMap.iteratedTotalIsoOfFinite G B
    (finite_singularBicomplex_antidiagonal K b)

/-- The comparison on a summand uses the two original inclusions in order. -/
theorem iteratedSingularTotalFromColumns_summand
    (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (p q r m n : ℤ) (hm : p + q = m) (hn : m + r = n) :
    (iteratedSingularTricomplex K).ιTotal₂₃ c c p q r n (by
        change p + (q + r) = n
        omega) ≫
        (iteratedSingularTotalFromColumns K b).hom.f n =
      ((S).map (((singularBicomplexFunctor k).obj K).ιTotal c p q m hm)).f r ≫
        ((singularBicomplexFunctor k).obj ((singularTotalFunctor k).obj K)).ιTotal c m r n hn := by
  let G : PresheafWithTransfers.{v} k ⥤ CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
    singularCoChains k
  let B := (singularBicomplexFunctor k).obj K
  unfold iteratedSingularTotalFromColumns
  exact HomologicalComplex₂.TotalMap.iteratedTotalIsoOfFinite_summand G B
    (finite_singularBicomplex_antidiagonal K b) p q r m n hm hn

end AlgebraicGeometry.PresheafWithTransfers

/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleTensorExact
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusOrdinaryKFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # K-flatness of the actual smooth étale reduced-torus cochains

Exact sheaf rows and exact sequential sheaf colimits feed the existing bounded-above
K-flat totalization theorem. No acyclicity of underlying presheaves is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

attribute [local instance] smoothEtaleIntegral_isMonoidal_W Sheaf.monoidalCategory
  Sheaf.braidedCategory Sheaf.monoidalPreadditive

local notation "S" => SmoothEtaleIntegralSheaves k
local notation "a" => smoothEtaleIntegralSheafify k

/-- The native sheafification of the original cochains, without a replacement model. -/
abbrev reducedTorusEtaleOrdinaryCochains (q : ℕ) : CochainComplex S ℤ :=
  ((a).mapHomologicalComplex (.up ℤ)).obj (reducedTorusOrdinaryIntegralCochains k q)

/-- Exact sheafification retains the original strict upper bound. -/
instance reducedTorusEtaleOrdinaryCochains_isStrictlyLE (q : ℕ) :
    (reducedTorusEtaleOrdinaryCochains k q).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  exact (a).map_isZero (reducedTorusOrdinaryIntegralCochains_isZero_X k q n hn)

/-- Sequential colimits of acyclic sheaf complexes are acyclic by the exact reflector. -/
theorem smoothEtaleIntegral_acyclic_sequentialColimit
    (E : ℕ ⥤ CochainComplex S ℤ) (s : Cocone E) (hs : IsColimit s)
    (hE : ∀ j, (E.obj j).Acyclic) : s.pt.Acyclic := by
  let := ModuleCat.hasExactFilteredColimits.{u + 1} ℤ ℕ
  let : HasExactColimitsOfShape ℕ S :=
    (sheafificationAdjunction (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
      (ModuleCat.{u + 1} ℤ)).hasExactColimitsOfShape ℕ
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let H := HomologicalComplex.homologyFunctor S (.up ℤ) n
  let := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := S) (J := ℕ) (.up ℤ) n
  exact IsColimit.isZero_pt (isColimitOfPreserves H hs)
    (Functor.isZero _ (fun j =>
      (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp (hE j n)))

/-- Tensor with any sheaf preserves the sequential colimits used in the truncation proof. -/
theorem smoothEtaleIntegralTensorLeft_preservesSequentialColimits (M : S) :
    PreservesColimitsOfShape ℕ (tensorLeft M) := by
  let P := M.obj
  let e : (a).obj P ≅ M :=
    asIso ((sheafificationAdjunction
      (SmoothSite.etaleTopology (Spec (CommRingCat.of k))) (ModuleCat.{u + 1} ℤ)).counit.app M)
  let := smoothEtaleIntegralTensorRight_preservesColimitsOfShape k P ℕ
  let : PreservesColimitsOfShape ℕ (tensorRight M) :=
    preservesColimitsOfShape_of_natIso ((tensoringRight S).mapIso e)
  exact preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm

-- Construct each total coproduct from the cached colimit record before elaborating KFlat.
local instance etaleKFlat_smallColimits : HasColimitsOfSize.{0, 0} S := inferInstance

local instance etaleKFlat_hasTotal
    (B : HomologicalComplex₂ S (.up ℤ) (.up ℤ)) : B.HasTotal (.up ℤ) :=
  fun _ => (@HasColimitsOfSize.has_colimits_of_shape S _
    (etaleKFlat_smallColimits k) (Discrete _) _).has_colimit _

local instance etaleKFlat_tensorAdditive : (curriedTensor S).Additive := inferInstance

local instance etaleKFlat_tensorObjAdditive (M : S) :
    ((curriedTensor S).obj M).Additive := inferInstance

local instance etaleKFlat_hasMapBifunctor (K L : CochainComplex S ℤ) :
    HomologicalComplex.HasMapBifunctor K L (curriedTensor S) (.up ℤ) :=
  etaleKFlat_hasTotal k _

/-- The concrete bounded-above sheafified reduced-torus complex is K-flat. -/
theorem reducedTorusEtaleOrdinaryCochains_kFlat (q : ℕ) :
    CochainComplex.KFlatBifunctor.KFlat (curriedTensor S)
      (reducedTorusEtaleOrdinaryCochains k q) := by
  apply CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE (curriedTensor S)
    (reducedTorusEtaleOrdinaryCochains k q) 0
  · exact smoothEtaleIntegralTensorLeft_preservesSequentialColimits k
  · exact smoothEtaleIntegral_acyclic_sequentialColimit k
  · intro n
    apply CochainComplex.KFlatBifunctor.kFlat_single_of_exact (curriedTensor S)
      ((reducedTorusEtaleOrdinaryCochains k q).X n) n
    intro G hG
    exact smoothEtaleIntegralRow_acyclic k
      ((reducedTorusOrdinaryIntegralCochains k q).X n) G hG

end AlgebraicGeometry.PresheafWithTransfers

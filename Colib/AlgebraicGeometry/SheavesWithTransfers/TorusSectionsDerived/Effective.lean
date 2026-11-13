/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.SmallSiteDerivedDetection
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.Acyclic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.EvaluationHom
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionInvariance
import Colib.AlgebraicGeometry.Sites.Smooth.FiniteKrullDimension
import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
import StacksFrontier.AlgebraicGeometry.Variety.FibreDimensionTotal

/-!
# Total derived torus sections of effective coefficients

The cohomological cutoff is uniform over the small Nisnevich site of a
fixed smooth scheme. Bounded comparison at that cutoff proves the
original upper bound. The two adjacent truncation maps then identify
each cohomology sheaf with the torus sections of the original
cohomology coefficient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe w w' u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S

private theorem parameterNeighborhood_krullDim_le (X : SmoothSite S)
    (V : EtaleSeparatedFiniteType X.left) (d : ℕ)
    (hd : topologicalKrullDim (SmoothSite.product X G).left ≤ d) :
    topologicalKrullDim
      (SmoothSite.product ((EtaleSeparatedFiniteType.toSmoothSite X).obj V) G).left ≤ d := by
  let Y := (EtaleSeparatedFiniteType.toSmoothSite X).obj V
  let f := (SmoothSite.productMap (EtaleSeparatedFiniteType.toBase X V) (𝟙 G)).left
  let : Etale f := EtaleSeparatedFiniteType.parameterProduct_etale X G V
  change topologicalKrullDim (SmoothSite.product Y G).left ≤ d
  rw [AlgebraicGeometry.topologicalKrullDim_eq_iSup_dimAt]
  exact iSup_le (fun x => (AlgebraicGeometry.topologicalKrullDimAt_eq_of_etale f x).trans_le
    ((topologicalKrullDimAt_le_topologicalKrullDim (f x)).trans hd))

private abbrev invariantSheafProperty : ObjectProperty (SheafWithTransfers.{u + 1} k) :=
  fun F => F.obj.IsA1Invariant

private instance : (invariantSheafProperty k).IsClosedUnderIsomorphisms where
  of_iso e hF := hF.of_iso ((SheafWithTransfers.forget k).mapIso e)

private instance : (invariantSheafProperty k).ContainsZero where
  exists_zero := by
    obtain ⟨F, hF⟩ := HasZeroObject.zero (C := SheafWithTransfers.{u + 1} k)
    exact ⟨F, hF, isA1Invariant_of_isZero ((SheafWithTransfers.forget k).map_isZero hF)⟩

variable [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [PerfectField k]

/-- Actual total derived torus sections retain the upper bound of a
bounded-above complex with A¹-invariant cohomology sheaves. -/
theorem torusSectionsDerived_isLE_of_isLE_of_isA1Invariant
    (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) (b : ℤ) [K.IsLE b]
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).obj.IsA1Invariant) :
    ((torusSectionsDerivedFunctor k).obj K).IsLE b := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  apply isZero_of_isZero_smallUnderlyingSheaf k
  intro X
  obtain ⟨d, hd⟩ := SmoothSite.exists_nat_topologicalKrullDim_le k (SmoothSite.product X G)
  let a : ℤ := i - (d : ℤ)
  let t : Triangulated.TStructure (DerivedCategory (SheafWithTransfers.{u + 1} k)) :=
    DerivedCategory.TStructure.t
  let L := (t.truncGE a).obj K
  let R := torusSectionsDerivedFunctor k
  let f := R.map ((t.truncGEπ a).app K)
  let H := DerivedCategory.homologyFunctor (SheafWithTransfers.{u + 1} k) i
  let U := smallUnderlyingSheaf k X
  let : L.IsGE a := inferInstanceAs (((t.truncGE a).obj K).IsGE a)
  let : L.IsLE b := inferInstanceAs (((t.truncGE a).obj K).IsLE b)
  have hL (q : ℤ) : ((DerivedCategory.homologyFunctor _ q).obj L).obj.IsA1Invariant :=
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj (invariantSheafProperty k) K hK a q
  let : (R.obj L).IsLE b := torusSectionsDerived_isLE_of_isGE_of_isLE k L a b hL
  let : IsIso (U.map (H.map f)) := isIso_smallUnderlyingSheaf_homologyMap_of_bijective_hom k X i f
    (fun V => by
      let Y := (EtaleSeparatedFiniteType.toSmoothSite X).obj V
      let : HasProjectiveDimensionLE
          ((transferRepresentable k).obj (Cor.mk (SmoothSite.product Y G))) d :=
        transferRepresentable_hasProjectiveDimensionLE_of_krullDim_le k (SmoothSite.product Y G)
          d (parameterNeighborhood_krullDim_le k X V d hd)
      exact bijective_comp_torusSectionsDerived_map_truncGEπ k Y K d i)
  exact (U.map_isZero (DerivedCategory.isZero_of_isLE (R.obj L) b i hi)).of_iso
    (asIso (U.map (H.map f)))

/-- The actual cohomology of total derived torus sections is the torus
sections of the original cohomology coefficient on bounded-above
A¹-invariant inputs. -/
@[no_expose]
def torusSectionsDerivedHomologyIsoOfIsLEOfIsA1Invariant
    (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) (b : ℤ) [K.IsLE b]
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).obj.IsA1Invariant)
    (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj ((torusSectionsDerivedFunctor k).obj K) ≅
      (torusSectionsFunctor k).obj ((DerivedCategory.homologyFunctor _ i).obj K) := by
  let R := torusSectionsDerivedFunctor k
  let A := SheafWithTransfers.{u + 1} k
  let t : Triangulated.TStructure (DerivedCategory A) := DerivedCategory.TStructure.t
  let H := DerivedCategory.homologyFunctor A i
  let L := (t.truncLE i).obj K
  let V := (t.truncGE (i + 1)).obj K
  let W := (t.truncLE (i - 1)).obj L
  let M := (t.truncGE i).obj L
  let ι : L ⟶ K := (t.truncLEι i).app K
  let π : L ⟶ M := (t.truncGEπ i).app L
  let : V.IsGE (i + 1) := inferInstanceAs (((t.truncGE (i + 1)).obj K).IsGE (i + 1))
  let : W.IsLE (i - 1) := inferInstanceAs (((t.truncLE (i - 1)).obj L).IsLE (i - 1))
  have hL (j : ℤ) : ((DerivedCategory.homologyFunctor _ j).obj L).obj.IsA1Invariant :=
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj (invariantSheafProperty k) K hK i j
  have hW (j : ℤ) : ((DerivedCategory.homologyFunctor _ j).obj W).obj.IsA1Invariant :=
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj (invariantSheafProperty k) L hL _ j
  have hV : (R.obj V).IsGE (i + 1) := torusSectionsDerived_isGE k V _
  have hW' : (R.obj W).IsLE (i - 1) :=
    torusSectionsDerived_isLE_of_isLE_of_isA1Invariant k W _ hW
  let : IsIso (H.map (R.map ι)) :=
    DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _
      (R.map_distinguished _ (t.triangleLEGE_distinguished i (i + 1) rfl K))
      i (i + 1) hV (by omega)
  let : IsIso (H.map (R.map π)) :=
    DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ _
      (R.map_distinguished _ (t.triangleLEGE_distinguished (i - 1) i (by omega) L))
      i (i - 1) hW' (by omega)
  let e : M ≅ (DerivedCategory.singleFunctor _ i).obj (H.obj K) :=
    (DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor i).app K
  exact (asIso (H.map (R.map ι))).symm ≪≫ asIso (H.map (R.map π)) ≪≫
    H.mapIso (R.mapIso e ≪≫ torusSectionsDerivedSingleIso k _
      (torusSectionsFunctor_rightAcyclic_of_perfect k _ (hK i)) i) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A i).app _

/-- The original A¹-invariance condition is preserved by total derived
torus sections on bounded-above effective inputs. -/
theorem torusSectionsDerived_homology_isA1Invariant_of_isLE
    (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) (b : ℤ) [K.IsLE b]
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).obj.IsA1Invariant)
    (i : ℤ) :
    PresheafWithTransfers.IsA1Invariant
      (((DerivedCategory.homologyFunctor _ i).obj ((torusSectionsDerivedFunctor k).obj K)).obj) :=
  let e := torusSectionsDerivedHomologyIsoOfIsLEOfIsA1Invariant k K b hK i
  (withParameter_isA1Invariant _ (hK i) G).of_iso
    ((SheafWithTransfers.forget k).mapIso e.symm)

end AlgebraicGeometry.SheafWithTransfers

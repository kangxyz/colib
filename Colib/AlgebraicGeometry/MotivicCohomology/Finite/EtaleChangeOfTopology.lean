/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Complex
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Map
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ChangeOfTopology

/-!
# Étale change of topology for the actual finite motivic complex

Apply the ordinary Nisnevich-to-étale sheafification functor degreewise to the
actual motivic sheaf complex and its multiplication cone. The comparison map
is the native sheafification unit in each degree. This is a chain-level
construction; it does not identify the resulting complex with roots of unity
or assert that the unit is a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

/-- The actual integral motivic complex after degreewise étale sheafification. -/
def motivicEtaleSheafComplex (q : ℕ) :
    CochainComplex (Sheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}) ℤ :=
  ((SmoothSite.nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℤ)).obj (motivicSheafComplex k q)

/-- Étale sheafification of the actual finite-coefficient motivic complex. -/
def motivicFiniteEtaleSheafComplex (q n : ℕ) :
    CochainComplex (Sheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}) ℤ :=
  ((SmoothSite.nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℤ)).obj (motivicFiniteSheafComplex k q n)

/-- The actual comparison map is the sheafification unit in every degree. -/
@[colib_tag "COL-1223",
  colib_ref "MVW2006" "Lecture 10, Definition 10.1, p. 75" "background"
    "Etale hypercohomology of motivic complexes; only the chain unit is constructed here"]
def motivicFiniteEtaleComparison (q n : ℕ) :
    motivicFiniteSheafComplex k q n ⟶
      ((SmoothSite.etaleToNisnevichSheaf (Spec (.of k)) AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℤ)).obj (motivicFiniteEtaleSheafComplex k q n) where
  f i := (SmoothSite.nisnevichToEtaleSheafAdjunction
    (Spec (.of k)) AddCommGrpCat.{u + 1}).unit.app
      ((motivicFiniteSheafComplex k q n).X i)
  comm' i j _ := by
    exact ((SmoothSite.nisnevichToEtaleSheafAdjunction
      (Spec (.of k)) AddCommGrpCat.{u + 1}).unit.naturality
        ((motivicFiniteSheafComplex k q n).d i j)).symm

/-- The comparison is the canonical map to étale sheafification, not a chosen map. -/
theorem motivicFiniteEtaleComparison_f_hom (q n : ℕ) (i : ℤ) :
    ((motivicFiniteEtaleComparison k q n).f i).hom =
      toSheafify (SmoothSite.etaleTopology (Spec (.of k)))
        ((motivicFiniteSheafComplex k q n).X i).obj :=
  SmoothSite.nisnevichToEtaleSheafAdjunction_unit_app_hom
    (Spec (.of k)) AddCommGrpCat.{u + 1} ((motivicFiniteSheafComplex k q n).X i)

/-- Additive étale sheafification commutes with the actual multiplication cone. -/
@[colib_tag "COL-1223",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean" "ingredient"
    "Additive mapping-cone comparison; integral and signed connecting morphisms retained"]
def motivicFiniteEtaleSheafComplexIso (q n : ℕ) :
    motivicFiniteEtaleSheafComplex k q n ≅
      CochainComplex.finiteCoefficients (motivicEtaleSheafComplex k q) n :=
  CochainComplex.finiteCoefficients.mapIso
    (SmoothSite.nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1})
    (motivicSheafComplex k q) n

/-- Étale cone comparison preserves the actual integral-reduction map. -/
theorem motivicFiniteEtaleSheafComplexIso_integral (q n : ℕ) :
    ((SmoothSite.nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (.up ℤ)).map (CochainComplex.finiteCoefficients.integral (motivicSheafComplex k q) n) ≫
      (motivicFiniteEtaleSheafComplexIso k q n).hom =
    CochainComplex.finiteCoefficients.integral (motivicEtaleSheafComplex k q) n :=
  CochainComplex.finiteCoefficients.mapIso_integral
    (SmoothSite.nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1})
    (motivicSheafComplex k q) n

/-- Étale cone comparison preserves the original signed Bockstein morphism. -/
theorem motivicFiniteEtaleSheafComplexIso_bockstein (q n : ℕ) :
    ((SmoothSite.nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (.up ℤ)).map (CochainComplex.finiteCoefficients.bockstein (motivicSheafComplex k q) n) ≫
      (((SmoothSite.nisnevichToEtaleSheaf (Spec (.of k))
        AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (.up ℤ)).commShiftIso (1 : ℤ)).hom.app (motivicSheafComplex k q) =
    (motivicFiniteEtaleSheafComplexIso k q n).hom ≫
      CochainComplex.finiteCoefficients.bockstein (motivicEtaleSheafComplex k q) n :=
  CochainComplex.finiteCoefficients.mapIso_bockstein
    (SmoothSite.nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1})
    (motivicSheafComplex k q) n

end AlgebraicGeometry.PresheafWithTransfers

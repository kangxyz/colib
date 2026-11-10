/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Underlying
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Exactness
public import Colib.AlgebraicGeometry.Simplex.SheafifiedChains

/-!
# Degreewise sheafified singular complexes with actual transfers

The proved additive transfer-preserving Nisnevich sheafification is applied to
every term and differential. Its transfer-natural unit is a chain map, and
the construction remains functorial in the input transfer presheaf. Chain
degree `r` can also be placed in cochain degree `q-r` before sheafification.
No reduced torus, normalization, or motivic-complex identification is assumed.

Adapted from `Motivic/Transfers/SingularComplex/Sheafification.lean` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`, using Colib's actual transfer
sheafification and literal-product ordinary singular chains. The original large
coefficient universe and the native sheafification assumptions are explicit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
/-- Apply actual transfer-preserving sheafification in each singular chain degree. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/SingularComplex/Sheafification.lean: singularSheafFunctor"
  "adaptation" "Actual degreewise Nisnevich sheafification with transfers"]
def singularSheafFunctor : PresheafWithTransfers.{u + 1} k ⥤
    ChainComplex (SheafWithTransfers.{u + 1} k) ℕ :=
  singularComplexFunctor ⋙ (nisnevichSheafify k).mapHomologicalComplex (ComplexShape.down ℕ)

/-- The singular chain complex of actual Nisnevich sheaves with transfers. -/
abbrev singularSheafComplex (P : PresheafWithTransfers.{u + 1} k) :
    ChainComplex (SheafWithTransfers.{u + 1} k) ℕ :=
  (singularSheafFunctor k).obj P

@[simp]
theorem singularSheafComplex_X (P : PresheafWithTransfers.{u + 1} k) (n : ℕ) :
    (singularSheafComplex k P).X n = (nisnevichSheafify k).obj ((singularComplex P).X n) := rfl

@[simp]
theorem singularSheafComplex_d (P : PresheafWithTransfers.{u + 1} k) (i j : ℕ) :
    (singularSheafComplex k P).d i j =
      (nisnevichSheafify k).map ((singularComplex P).d i j) := rfl

/-- Coefficient morphisms induce actual maps of sheaf complexes with transfers. -/
@[simp]
theorem singularSheafFunctor_map_f {P Q : PresheafWithTransfers.{u + 1} k}
    (η : P ⟶ Q) (n : ℕ) :
    ((singularSheafFunctor k).map η).f n =
      (nisnevichSheafify k).map ((singularComplexMap η).f n) := rfl

/-- The degreewise transfer-natural unit is a genuine map of singular complexes. -/
def singularSheafUnit : singularComplexFunctor ⟶ singularSheafFunctor k ⋙
    (SheafWithTransfers.forget k).mapHomologicalComplex (ComplexShape.down ℕ) where
  app P :=
    { f n := toNisnevichSheafify k ((singularComplex P).X n)
      comm' i j _ := (toNisnevichSheafify_naturality k ((singularComplex P).d i j)).symm }
  naturality P Q η := by
    ext n : 1
    exact toNisnevichSheafify_naturality k ((singularComplexMap η).f n)

@[simp]
theorem singularSheafUnit_app_f (P : PresheafWithTransfers.{u + 1} k) (n : ℕ) :
    ((singularSheafUnit k).app P).f n =
      toNisnevichSheafify k ((singularComplex P).X n) := rfl

/-- Place the transfer complex in degrees `q-r`, then sheafify degreewise. -/
def singularSheafCochainFunctor (q : ℕ) : PresheafWithTransfers.{u + 1} k ⥤
    CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  singularCochainFunctor q ⋙ (nisnevichSheafify k).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The placed, degreewise-sheafified complex of actual sheaves with transfers. -/
abbrev singularSheafCochainComplex (P : PresheafWithTransfers.{u + 1} k) (q : ℕ) :
    CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  (singularSheafCochainFunctor k q).obj P

/-- The term at `q-r` is exactly sheafification of the original degree-`r` transfer presheaf. -/
def singularSheafCochainXIso (P : PresheafWithTransfers.{u + 1} k) (q r : ℕ) :
    (singularSheafCochainComplex k P q).X (((q : ℤ) - r)) ≅
      (nisnevichSheafify k).obj ((singularComplex P).X r) :=
  (nisnevichSheafify k).mapIso (singularCochainXIso P q r)

/-- Sheafified terms above the stated weight vanish. -/
theorem isZero_singularSheafCochainComplex_X (P : PresheafWithTransfers.{u + 1} k)
    (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((singularSheafCochainComplex k P q).X i) :=
  (nisnevichSheafify k).map_isZero (isZero_singularCochainComplex_X P q i hi)

/-- The placed differential is sheafification of the exact alternating differential. -/
theorem singularSheafCochainComplex_d (P : PresheafWithTransfers.{u + 1} k) (q r : ℕ) :
    (singularSheafCochainComplex k P q).d (((q : ℤ) - (r + 1)))
        (((q : ℤ) - r)) =
      (singularSheafCochainXIso k P q (r + 1)).hom ≫
        (nisnevichSheafify k).map ((singularComplex P).d (r + 1) r) ≫
        (singularSheafCochainXIso k P q r).inv := by
  change (nisnevichSheafify k).map ((singularCochainComplex P q).d _ _) = _
  rw [singularCochainComplex_d]
  simp only [Functor.map_comp]
  rfl

/-- The placed complex has the same canonical, transfer-natural sheafification unit. -/
def singularSheafCochainUnit (q : ℕ) : singularCochainFunctor q ⟶
    singularSheafCochainFunctor k q ⋙
      (SheafWithTransfers.forget k).mapHomologicalComplex (ComplexShape.up ℤ) where
  app P :=
    { f n := toNisnevichSheafify k ((singularCochainComplex P q).X n)
      comm' i j _ :=
        (toNisnevichSheafify_naturality k ((singularCochainComplex P q).d i j)).symm }
  naturality P Q η := by
    ext n : 1
    exact toNisnevichSheafify_naturality k (((singularCochainFunctor q).map η).f n)

section OrdinaryComparison

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

/-- Forgetting transfers commutes with sheafification of the entire singular complex. -/
def singularSheafUnderlyingIso (P : PresheafWithTransfers.{u + 1} k) :
    ((toPresheaf k ⋙ presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (singularComplex P) ≅
    ((SheafWithTransfers.toSheaf k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (singularSheafComplex k P) :=
  (NatIso.mapHomologicalComplex (nisnevichSheafificationUnderlyingIso k)
    (ComplexShape.down ℕ)).app (singularComplex P)

/-- Forgetting transfers identifies this complex with the pre-existing ordinary
Nisnevich-sheafified singular complex, using the identity on the same literal product sections. -/
def singularSheafOrdinaryIso (P : PresheafWithTransfers.{u + 1} k) :
    ((SheafWithTransfers.toSheaf k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (singularSheafComplex k P) ≅
      (AlgebraicSimplex.sheafifiedSingularChainsFunctor k
        (SmoothSite.nisnevichTopology (Spec (.of k)))).obj ((toPresheaf k).obj P) :=
  (singularSheafUnderlyingIso k P).symm ≪≫
    ((presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
        (singularComplexUnderlyingIso P)

/-- The ordinary comparison is natural in every original coefficient morphism. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/SingularComplex/Sheafification.lean: singularSheafOrdinaryIso"
  "adaptation" "Naturality of the actual ordinary underlying comparison"]
def singularSheafOrdinaryNatIso :
    singularSheafFunctor k ⋙
        (SheafWithTransfers.toSheaf k).mapHomologicalComplex (ComplexShape.down ℕ) ≅
      toPresheaf k ⋙ AlgebraicSimplex.sheafifiedSingularChainsFunctor k
        (SmoothSite.nisnevichTopology (Spec (.of k))) :=
  (Functor.isoWhiskerLeft singularComplexFunctor
      (NatIso.mapHomologicalComplex (nisnevichSheafificationUnderlyingIso k)
        (ComplexShape.down ℕ))).symm ≪≫
    Functor.isoWhiskerRight singularComplexUnderlyingNatIso
      ((presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.down ℕ))

end OrdinaryComparison

end AlgebraicGeometry.PresheafWithTransfers

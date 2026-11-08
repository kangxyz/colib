module

import Colib.AlgebraicGeometry.Sites.Nisnevich.Basic
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

example {X : Scheme.{u}} {ι : Type v} [Small.{u} ι]
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ Nisnevich.precoverage X ↔
      (∀ i, Etale (f i)) ∧ IsCompletelyDecomposedFamily f :=
  Nisnevich.ofArrows_mem_precoverage_iff_isCompletelyDecomposedFamily f

example {X : Scheme.{u}} {ι : Type v} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ Nisnevich.precoverage X ↔
      (∀ i, Etale (f i)) ∧
        ∀ x : X, ∃ (i : ι) (y : Y i), f i y = x ∧ IsIso ((f i).residueFieldMap y) :=
  Nisnevich.ofArrows_mem_precoverage_iff f

example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Presieve.singleton f ∈ Nisnevich.precoverage Y :=
  Precoverage.mem_coverings_of_isIso f

example : Nisnevich.precoverage.{u}.IsStableUnderBaseChange := inferInstance

example : Nisnevich.precoverage.{u}.IsStableUnderComposition := inferInstance

example : Scheme.zariskiTopology.{u} ≤ Nisnevich.topology :=
  Nisnevich.zariskiTopology_le_topology

example : Nisnevich.topology.{u} ≤ Scheme.etaleTopology :=
  Nisnevich.topology_le_etaleTopology

example (K : Type u) [Field K] (R : Sieve (Spec (.of K))) :
    R ∈ Nisnevich.topology _ ↔ R = ⊤ := Nisnevich.mem_topology_iff K R

example (K : Type u) [Field K] {R : Presieve (Spec (.of K))}
    (hR : R ∈ Nisnevich.precoverage _) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of K)), R f ∧
      ∃ s : Spec (.of K) ⟶ Y, s ≫ f = 𝟙 _ :=
  Nisnevich.exists_section_of_mem_precoverage K hR

example (K : Type u) [Field K] (X : Scheme.{u}) :
    (Nisnevich.fieldPoint K).fiber.obj X = (Spec (.of K) ⟶ X) := rfl

example (S : Scheme.{u}) : Smooth (Scheme.SmoothSite.base S).hom := inferInstance

example (S : Scheme.{u}) (X : Scheme.SmoothSite S) :
    LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom := Scheme.SmoothSite.finiteType X

example (S : Scheme.{u}) {X Y Z : Scheme.SmoothSite S} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale f.left] : HasPullback f g := inferInstance

example (S : Scheme.{u}) {X Y Z : Scheme.SmoothSite S} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale f.left] : PreservesLimit (cospan f g) (Scheme.SmoothSite.forgetScheme S) :=
  inferInstance

example (S : Scheme.{u}) {X : Scheme.SmoothSite S} {ι : Type v}
    {Y : ι → Scheme.SmoothSite S} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ Scheme.SmoothSite.nisnevichPrecoverage S X ↔
      (∀ i, Etale (f i).left) ∧ ∀ x : X.left,
        ∃ (i : ι) (y : (Y i).left), (f i).left y = x ∧
          IsIso ((f i).left.residueFieldMap y) :=
  Scheme.SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff f

example (S : Scheme.{u}) : (Scheme.SmoothSite.forget S).IsContinuous
    (Scheme.SmoothSite.nisnevichTopology S) (Nisnevich.topology.over S) := inferInstance

example (S : Scheme.{u}) {X : Scheme.SmoothSite S} {R : Sieve X} :
    R ∈ Scheme.SmoothSite.nisnevichTopology S X ↔
      ∃ Q ∈ Scheme.SmoothSite.nisnevichPrecoverage S X, Q ≤ R :=
  Scheme.SmoothSite.mem_nisnevichTopology_iff

example (S : Scheme.{u}) (A : Type v) [Category A] :
    Sheaf (Nisnevich.topology.over S) A ⥤
      Sheaf (Scheme.SmoothSite.nisnevichTopology S) A :=
  Scheme.SmoothSite.restrictNisnevichSheaf S A

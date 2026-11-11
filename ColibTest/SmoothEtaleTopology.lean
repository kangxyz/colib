module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.Topology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u v w

example (S : Scheme.{u}) {X : SmoothSite S} {ι : Type v}
    {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ SmoothSite.etalePrecoverage S X ↔
      (∀ i, Etale (f i).left) ∧
        ∀ x : X.left, ∃ (i : ι) (y : (Y i).left), (f i).left y = x :=
  SmoothSite.ofArrows_mem_etalePrecoverage_iff f

example (S : Scheme.{u}) : (SmoothSite.etalePrecoverage S).HasPullbacks := inferInstance

example (S : Scheme.{u}) :
    (SmoothSite.etalePrecoverage S).IsStableUnderBaseChange := inferInstance

example (S : Scheme.{u}) :
    (SmoothSite.forgetScheme S).IsContinuous
      (SmoothSite.etaleTopology S) Scheme.etaleTopology := inferInstance

example (S : Scheme.{u}) :
    SmoothSite.nisnevichTopology S ≤ SmoothSite.etaleTopology S :=
  SmoothSite.nisnevichTopology_le_etaleTopology S

example (S : Scheme.{u}) (A : Type v) [Category.{w} A]
    (F : Sheaf (SmoothSite.etaleTopology S) A) :
    ((SmoothSite.etaleToNisnevichSheaf S A).obj F).obj = F.obj := rfl

example (S : Scheme.{u}) (A : Type v) [Category.{w} A]
    {F G : Sheaf (SmoothSite.etaleTopology S) A} (f : F ⟶ G) :
    ((SmoothSite.etaleToNisnevichSheaf S A).map f).hom = f.hom := rfl

example (S : Scheme.{u}) (A : Type v) [Category.{w} A] :
    (SmoothSite.etaleToNisnevichSheaf S A).Full := inferInstance

example (S : Scheme.{u}) (A : Type v) [Category.{w} A] :
    (SmoothSite.etaleToNisnevichSheaf S A).Faithful := inferInstance

/- Source-only candidate: inherit original finite cover and coordinate charts on fixed U. -/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ProjectiveLine
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

variable {R : Type u} [CommRing R] {X U Y : Scheme.{u}}
  (k : U ⟶ X) (p : X ⟶ Spec (.of R))
  (π : X ⟶ projectiveLine R)
  (hπ : π ≫ (projectiveLine R ↘ Spec (.of R)) = p)

/-- Closedness of the actual model inclusion preserves the original finite cover. -/
instance finite_projectiveLineCover_clopenModel [IsClosedImmersion k] [IsFinite π] :
    IsFinite (k ≫ π) := inferInstance

theorem projectiveLineCover_clopenModel_structure :
    (k ≫ π) ≫ (projectiveLine R ↘ Spec (.of R)) = k ≫ p := by
  rw [Category.assoc, hπ]

variable (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial R)))

/-- Retained and independent chart coordinate equations survive the literal model pullback. -/
theorem affineChart_clopenModel_comp_XChart
    (hj : j ≫ π = a ≫ projectiveLineXChart R) :
    pullback.fst k j ≫ (k ≫ π) =
      (pullback.snd k j ≫ a) ≫ projectiveLineXChart R := by
  rw [← Category.assoc, pullback.condition, Category.assoc, hj, Category.assoc]

theorem affineChart_clopenModel_structure
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) = j ≫ p) :
    (pullback.snd k j ≫ a) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      pullback.fst k j ≫ (k ≫ p) := by
  rw [Category.assoc, ha, ← Category.assoc, ← pullback.condition, Category.assoc]

instance affineChart_clopenModel_etale [IsOpenImmersion k] [Etale a] :
    Etale (pullback.snd k j ≫ a) := inferInstance

end AlgebraicGeometry.Scheme

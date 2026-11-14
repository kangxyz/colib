/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOpenWeak
public import Colib.CategoryTheory.Waldhausen.ExactFunctorIso

/-! # Exact functors commuting with literal open restriction

A natural isomorphism between the two paths around the square supplies
preservation of relative weak equivalences. The functors and the underlying
perfect categories themselves are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X V Y : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]

local notation:max "Perf[" Z "]" =>
  ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
    (X := LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Z)))
local notation:max "W[" Z "]" =>
  RingedSpace.perfectComplexesWaldhausen
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Z))
local notation:max "R[" g "]" => perfectComplexesRestrictOpenImmersion g

variable {F : Perf[X] ⥤ Perf[Y]} {G : Perf[U] ⥤ Perf[V]}
  (hf : IsExact (W[X]).cof (W[X]).weq (W[Y]).cof (W[Y]).weq F)
  (hg : IsExact (W[U]).cof (W[U]).weq (W[V]).cof (W[V]).weq G)

include hf hg in
/-- A fine exact square gives coarse exactness for its unchanged base functor. -/
theorem perfectOpen_coarseExact_of_restrictIso
    (e : F ⋙ R[k] ≅ R[j] ⋙ G) :
    IsExact (perfectOpenWeakWaldhausen j).cof (perfectOpenWeakWaldhausen j).weq
      (perfectOpenWeakWaldhausen k).cof (perfectOpenWeakWaldhausen k).weq F where
  zero := hf.zero
  cofibration := hf.cofibration
  pushout := hf.pushout
  weak f h := by
    change (W[V]).weq ((F ⋙ R[k]).map f)
    have h' : (W[U]).weq ((R[j]).map f) := h
    have hG : (W[V]).weq ((R[j] ⋙ G).map f) := hg.weak _ h'
    let a : Arrow.mk ((F ⋙ R[k]).map f) ≅ Arrow.mk ((R[j] ⋙ G).map f) :=
      Arrow.isoMk (e.app _) (e.app _) (e.hom.naturality f).symm
    exact ((W[V]).weq.arrow_mk_iso_iff a).2 hG

/-- Lift an isomorphism of the actual cochain functors to a square on the
unchanged perfect full subcategories. -/
def perfectOpenRestrictIso_of_complexIso
    (e : (F ⋙ R[k]) ⋙ ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := V.toRingedSpace)) ≅
      (R[j] ⋙ G) ⋙ ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := V.toRingedSpace))) :
    F ⋙ R[k] ≅ R[j] ⋙ G :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk
      (P := RingedSpace.IsPerfectComplex (X := V.toRingedSpace)) (e.app K))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact e.hom.naturality f)

end AlgebraicGeometry.Scheme.Modules

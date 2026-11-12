module
import Colib.KTheory.Waldhausen.Iterated.InverseImageModelDiagram
noncomputable section
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen.IteratedS.InverseImageModelDiagram
universe u v w
variable {I : Type u} [Category.{v} I] {A B : I ⥤ WideSubcategory preservesZero.{w}}
  (S : A ⟶ B)
example : changeWeak S ≫ restriction S = S := factor S
example (i : I) : model S i ⟶ B.obj i := component S i
example {i j : I} (f : i ⟶ j) :
    IsExact (model S i).obj.waldhausen.cof (model S i).obj.waldhausen.weq
      (model S j).obj.waldhausen.cof (model S j).obj.waldhausen.weq (A.map f).hom.toFunctor :=
  map_exact S f
end

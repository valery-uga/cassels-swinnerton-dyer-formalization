import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks
import AllCharacteristics.OverlapCompositionGluing

/-!
# Descent of morphisms from glued schemes

A compatible morphism from every chart of `Scheme.GlueData` descends to its
glued scheme.  Keeping this construction abstract prevents clients from
unfolding a large concrete gluing datum while constructing the descended map.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

namespace Scheme.GlueData

universe u

/-- Descend compatible chart morphisms through a scheme gluing datum. -/
noncomputable def descTo (D : Scheme.GlueData.{u}) {Y : Scheme.{u}}
    (F : ∀ i : D.J, D.U i ⟶ Y)
    (hF : ∀ i j : D.J,
      D.f i j ≫ F i = D.t i j ≫ D.f j i ≫ F j) :
    D.glued ⟶ Y := by
  fapply Multicoequalizer.desc
  · exact F
  · rintro ⟨i, j⟩
    exact hF i j

/-- The descended map restricts to the specified map on each glued chart. -/
@[reassoc]
theorem ι_descTo (D : Scheme.GlueData.{u}) {Y : Scheme.{u}}
    (F : ∀ i : D.J, D.U i ⟶ Y)
    (hF : ∀ i j : D.J,
      D.f i j ≫ F i = D.t i j ≫ D.f j i ≫ F j)
    (i : D.J) :
    D.ι i ≫ D.descTo F hF = F i :=
  Multicoequalizer.π_desc _ _ _ _ _

end Scheme.GlueData

end AlgebraicGeometry

namespace AllCharacteristics.OverlapComposition

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {ι : Type u}
variable (U : ι → Scheme.{u}) (V : ι → ι → Scheme.{u})
variable (left : ∀ i j, V i j ⟶ U i) (right : ∀ i j, V i j ⟶ U j)
variable (swap : ∀ i j, V i j ⟶ V j i)
variable (hswap : ∀ i j, swap i j ≫ left j i = right i j)
variable (cross : ∀ i j k, pullback (left i j) (left i k) ⟶ V j k)
variable (hcross : ∀ i j k, cross i j k ≫ left j k =
  pullback.fst (left i j) (left i k) ≫ right i j)
variable (hcrossRight : ∀ i j k, cross i j k ≫ right j k =
  pullback.snd (left i j) (left i k) ≫ right i k)
variable [∀ i j, Mono (left i j)]
variable (hinv : ∀ i j, swap i j ≫ swap j i = 𝟙 (V i j))
variable [∀ i, IsIso (left i i)] (hself : ∀ i, swap i i = 𝟙 (V i i))
variable (hopen : ∀ i j, IsOpenImmersion (left i j))

/-- Promote two-sided overlap data with open left maps to scheme gluing data. -/
noncomputable def schemeGlueData : Scheme.GlueData where
  toGlueData := glueData U V left right swap hswap cross hcross hcrossRight hinv hself
  f_open i j := by
    change ι at i j
    change IsOpenImmersion (left i j)
    exact hopen i j

/-- Descend compatible chart maps from two-sided overlap data to its glued scheme.
The compatibility is stated with the named right overlap map, so clients do
not need to unfold the gluing datum's transition structure. -/
noncomputable def gluedDescTo {Y : Scheme.{u}}
    (F : ∀ i, U i ⟶ Y)
    (hF : ∀ i j, left i j ≫ F i = right i j ≫ F j) :
    (schemeGlueData U V left right swap hswap cross hcross hcrossRight hinv hself hopen).glued ⟶ Y :=
  AlgebraicGeometry.Scheme.GlueData.descTo
    (schemeGlueData U V left right swap hswap cross hcross hcrossRight hinv hself hopen) F
    (by
      intro i j
      change ι at i j
      change left i j ≫ F i = (swap i j ≫ left j i) ≫ F j
      rw [hswap]
      exact hF i j)

/-- The descended two-sided-overlap map has the prescribed chart restrictions. -/
@[reassoc]
theorem ι_gluedDescTo {Y : Scheme.{u}}
    (F : ∀ i, U i ⟶ Y)
    (hF : ∀ i j, left i j ≫ F i = right i j ≫ F j)
    (i : ι) :
    (schemeGlueData U V left right swap hswap cross hcross hcrossRight hinv hself hopen).ι i ≫
      gluedDescTo U V left right swap hswap cross hcross hcrossRight hinv hself hopen F hF = F i :=
  by
    change ι at i
    exact AlgebraicGeometry.Scheme.GlueData.ι_descTo
      (schemeGlueData U V left right swap hswap cross hcross hcrossRight hinv hself hopen)
      F _ i

end AllCharacteristics.OverlapComposition

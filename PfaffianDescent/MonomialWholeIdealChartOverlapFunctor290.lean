import PfaffianDescent.MonomialWholeIdealChartOverlap290
import PfaffianDescent.MonomialWholeIdealChartRepresentability288

noncomputable section
namespace PfaffianDescent
open CategoryTheory
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C : Fin n → (Fin m →₀ ℕ)) (k : Fin n)

/-- The determinant-unit overlap is a subfunctor of the actual represented first chart. -/
def monomialWholeIdealChartOverlapFunctor290 (hk : B k = 0) :
    CommAlgCat.{u} R ⥤ Type u where
  obj A := MonomialWholeIdealChartOverlap290 (A := A) B C
  map f := TypeCat.ofHom (monomialWholeIdealChartOverlapMap290 B C k hk f.hom.toRingHom)
  map_id A := by
    ext x
    change monomialWholeIdealChartOverlapMap290 B C k hk (RingHom.id A) x = x
    apply Subtype.ext
    exact monomialWholeIdealChartMap_id287 B k hk x.val
  map_comp f g := by
    ext x
    change monomialWholeIdealChartOverlapMap290 B C k hk
        (g.hom.toRingHom.comp f.hom.toRingHom) x =
      monomialWholeIdealChartOverlapMap290 B C k hk g.hom.toRingHom
        (monomialWholeIdealChartOverlapMap290 B C k hk f.hom.toRingHom x)
    apply Subtype.ext
    exact monomialWholeIdealChartMap_comp287 B k hk f.hom.toRingHom g.hom.toRingHom x.val

/-- The inclusion preserves the whole ideal, and commutes with arbitrary coefficient change. -/
def monomialWholeIdealChartOverlapInclusion290 (hk : B k = 0) :
    monomialWholeIdealChartOverlapFunctor290 R m n B C k hk ⟶
      monomialWholeIdealChartFunctor288 R m n B k hk where
  app _ := TypeCat.ofHom Subtype.val
  naturality := by
    intro X Y f
    rfl

end PfaffianDescent

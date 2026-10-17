import PfaffianDescent.VoisinDegreeElevenSerreIncidenceIdealAffineCover

/-! An actual common affine cover for two actual maps into covered schemes.
Every member factors through both chosen target charts. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {X Y T : Scheme.{u}} (U : X.OpenCover) (V : Y.OpenCover)
  (f : T ⟶ X) (g : T ⟶ Y)

def serreActualPairChartOpenCover : T.OpenCover :=
  (U.pullback₁ f).bind fun i => V.pullback₁ ((U.pullback₁ f).f i ≫ g)

def serreActualPairChartAffineCover : T.AffineOpenCover :=
  (serreActualPairChartOpenCover U V f g).affineRefinement

def serreActualPairChartLeftMap
    (k : (serreActualPairChartAffineCover U V f g).I₀) :
    Spec ((serreActualPairChartAffineCover U V f g).X k) ⟶ U.X k.1.1 :=
  ((serreActualPairChartOpenCover U V f g).X k.1).affineCover.f k.2 ≫
    (V.pullback₁ ((U.pullback₁ f).f k.1.1 ≫ g)).f k.1.2 ≫
      U.pullbackHom f k.1.1

def serreActualPairChartRightMap
    (k : (serreActualPairChartAffineCover U V f g).I₀) :
    Spec ((serreActualPairChartAffineCover U V f g).X k) ⟶ V.X k.1.2 :=
  ((serreActualPairChartOpenCover U V f g).X k.1).affineCover.f k.2 ≫
    V.pullbackHom ((U.pullback₁ f).f k.1.1 ≫ g) k.1.2

@[reassoc]
theorem serreActualPairChartLeftMap_factor
    (k : (serreActualPairChartAffineCover U V f g).I₀) :
    serreActualPairChartLeftMap U V f g k ≫ U.f k.1.1 =
      (serreActualPairChartAffineCover U V f g).f k ≫ f := by
  change (_ ≫ (V.pullback₁ ((U.pullback₁ f).f k.1.1 ≫ g)).f k.1.2 ≫
    U.pullbackHom f k.1.1) ≫ U.f k.1.1 =
      (_ ≫ ((V.pullback₁ ((U.pullback₁ f).f k.1.1 ≫ g)).f k.1.2 ≫
        (U.pullback₁ f).f k.1.1)) ≫ f
  simp only [Category.assoc, Scheme.Cover.pullbackHom_map]

@[reassoc]
theorem serreActualPairChartRightMap_factor
    (k : (serreActualPairChartAffineCover U V f g).I₀) :
    serreActualPairChartRightMap U V f g k ≫ V.f k.1.2 =
      (serreActualPairChartAffineCover U V f g).f k ≫ g := by
  change (_ ≫ V.pullbackHom ((U.pullback₁ f).f k.1.1 ≫ g) k.1.2) ≫
    V.f k.1.2 =
      (_ ≫ ((V.pullback₁ ((U.pullback₁ f).f k.1.1 ≫ g)).f k.1.2 ≫
        (U.pullback₁ f).f k.1.1)) ≫ g
  simp only [Category.assoc, Scheme.Cover.pullbackHom_map]

theorem serreActualPairChart_comap_eq
    (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (h : ∀ k : (serreActualPairChartAffineCover U V f g).I₀,
      I.comap (serreActualPairChartLeftMap U V f g k ≫ U.f k.1.1) =
        J.comap (serreActualPairChartRightMap U V f g k ≫ V.f k.1.2)) :
    I.comap f = J.comap g := by
  apply serreIncidenceIdeal_eq_of_affineCover _ _
    (serreActualPairChartAffineCover U V f g)
  intro k
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  rw [← serreActualPairChartLeftMap_factor, ← serreActualPairChartRightMap_factor]
  exact h k

end PfaffianDescent

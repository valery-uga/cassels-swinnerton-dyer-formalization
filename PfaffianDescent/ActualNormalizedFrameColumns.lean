import PfaffianDescent.AmbientTensorNormalizedChartSquare
import PfaffianDescent.QuarticConjugateJets

/-! SOURCE ONLY, UNVERIFIED. Equal actual normalized projective maps determine
all field coordinates. Hence column proportionality is derived from actual
support-point maps, not supplied as an unexplained matrix certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actual_normalized_ambient_point_coordinates_injective
    {A : Type u} [CommRing A] [Algebra K A]
    (x y : Fin 4 → A) (j : Fin 4) (hx : x j = 1) (hy : y j = 1)
    (h : ambientNormalizedCoordinateChartPoint (F := K) x j hx =
      ambientNormalizedCoordinateChartPoint (F := K) y j hy) : x = y := by
  let chart := Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
    (isHomogeneous_X K j) (by decide : 0 < 1)
  letI : IsOpenImmersion chart := by
    dsimp only [chart, Proj.awayι]
    infer_instance
  have hChart : Spec.map (CommRingCat.ofHom (ambientNormalizedCoordinateChartMap x j hx)) ≫ chart =
      Spec.map (CommRingCat.ofHom (ambientNormalizedCoordinateChartMap y j hy)) ≫ chart := h
  have hMaps := Spec.map_injective ((cancel_mono chart).mp hChart)
  funext r
  have hr := congrArg (fun a : CommRingCat.of
    (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 4) K) (X j)) ⟶
      CommRingCat.of A => a.hom (ambientChartCoordinate (R := K) j r)) hMaps
  exact (ambientNormalizedCoordinateChartMap_coordinate x j hx r).symm.trans
    (hr.trans (ambientNormalizedCoordinateChartMap_coordinate y j hy r))

/-- The actual support map in the common original chart determines each
supplied frame column. hN is only the nonzero normalizer used to write that
actual map; its final GL consumer must derive it from chart membership. -/
theorem actual_frame_columns_proportional_of_support_maps
    (b : Basis (Fin 4) K (Fin 4 → K)) (j : Fin 4)
    (hb : ∀ i, b i j = 1) (N : Matrix (Fin 4) (Fin 4) K)
    (rho : Equiv.Perm (Fin 4)) (hN : ∀ i, N j i ≠ 0)
    (hPoint : ∀ i,
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => N r i / N j i) j (by exact div_self (hN i)) =
      ambientNormalizedCoordinateChartPoint (F := K) (b (rho i)) j (hb (rho i))) :
    ∀ i r, N r i = N j i * b (rho i) r := by
  intro i r
  have hxy := actual_normalized_ambient_point_coordinates_injective
    (fun r => N r i / N j i) (b (rho i)) j (by exact div_self (hN i))
    (hb (rho i)) (hPoint i)
  have hr := congrFun hxy r
  have hm := (div_eq_iff (hN i)).mp hr
  exact hm.trans (mul_comm _ _)

end PfaffianDescent

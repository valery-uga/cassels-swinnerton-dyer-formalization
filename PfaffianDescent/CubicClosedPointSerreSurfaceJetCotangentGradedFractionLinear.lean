import PfaffianDescent.HomogeneousChartLinear

noncomputable section
namespace PfaffianDescent
open HomogeneousLocalization
universe u
attribute [local instance] homogeneousChartAlgebra

/-- Division by the fixed degree-one chart coordinate in degree three is linear. -/
def cubicClosedPointSerreSurfaceJetCotangent_gradedFractionLinear
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (G : ℕ → Submodule K A) [GradedRing G] (ell : G 1) :
    G 3 →ₗ[K] Away G (ell : A) where
  toFun q := Away.mk G ell.2 3 q (by simpa using q.2)
  map_add' q r := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk, HomogeneousLocalization.val_add, Submodule.coe_add]
    exact (Localization.add_mk_self _ _ _).symm
  map_smul' a q := by
    change Away.mk G ell.2 3 (a • (q : A)) _ =
      algebraMap K (Away G (ell : A)) a * Away.mk G ell.2 3 (q : A) _
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_mul, Away.val_mk, Submodule.coe_smul,
      Algebra.smul_def]
    change Localization.mk (algebraMap K A a * (q : A)) _ =
      algebraMap A (Localization (Submonoid.powers (ell : A))) (algebraMap K A a) *
        Localization.mk (q : A) _
    simpa only [Localization.mk_eq_mk', Algebra.smul_def] using
      (IsLocalization.mul_mk'_eq_mk'_of_mul
        (S := Localization (Submonoid.powers (ell : A)))
        (algebraMap K A a) (q : A) _).symm

/-- The literal field-valued fraction restriction, with its actual coefficient map. -/
def cubicClosedPointSerreSurfaceJetCotangent_gradedFractionRestriction
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (G : ℕ → Submodule K A) [GradedRing G] (ell : G 1)
    (g : Away G (ell : A) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap G (z := (ell : A))) =
      algebraMap K L) : G 3 →ₗ[K] L :=
  (show Away G (ell : A) →ₐ[K] L from
    { __ := g
      commutes' a := congrArg (fun f : K →+* L => f a) hbase }).toLinearMap.comp
    (cubicClosedPointSerreSurfaceJetCotangent_gradedFractionLinear G ell)

end PfaffianDescent

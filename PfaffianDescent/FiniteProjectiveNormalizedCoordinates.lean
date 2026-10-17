import PfaffianDescent.FiniteProjectiveChart
import PfaffianDescent.LinearNormalizedProjectivePoint
import PfaffianDescent.NormalizedProjectiveQuotientFactor

/-!
# Linear-normalized coordinates of a finite projective subscheme

This strengthens the coordinate construction by retaining the linear form
whose value is one on the whole finite scheme.  It is exactly the datum needed
to re-embed the same finite algebra in a smaller complete intersection.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

section
variable {K : Type u} [Field K] [Infinite K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite projective closed subscheme has generating homogeneous
coordinates, normalized by one ground-field linear form, and those
coordinates satisfy every equation of the ambient scheme. -/
theorem finite_projective_closed_subscheme_normalized_coordinates
    (I : HomogeneousIdeal (homogeneousSubmodule σ K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] :
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    ∃ (x : σ → Γ(Z, ⊤)) (ell : MvPolynomial σ K),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧
      ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
      ∀ (q : MvPolynomial σ K) (d : ℕ), q.IsHomogeneous d → q ∈ I.toIdeal →
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  obtain ⟨z, hz, g, hgs, hg, _⟩ := finite_projective_closed_subscheme_chart I i
  have hz' := hz
  obtain ⟨ell, hell, hellz⟩ := hz'
  have hell' : ell.IsHomogeneous 1 := hell
  have hellz' : Ideal.Quotient.mk I.toIdeal ell = z := hellz
  let x : σ → Γ(Z, ⊤) := fun j ↦ g (linearChartCoordinate I z hz j)
  have he : eval₂Hom (algebraMap K Γ(Z, ⊤)) x =
      g.comp (eval₂Hom
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
        (linearChartCoordinate I z hz)) := by
    apply RingHom.ext
    intro q
    change q.eval₂ (algebraMap K Γ(Z, ⊤)) x = g (q.eval₂ _ _)
    rw [hom_eval₂, hg]
  refine ⟨x, ell, ?_, hell', ?_, ?_⟩
  · rw [he]
    exact hgs.comp (eval₂_linearChartCoordinate_surjective I z hz)
  · change eval₂Hom (algebraMap K Γ(Z, ⊤)) x ell = 1
    rw [he, RingHom.comp_apply]
    change g (ell.eval₂
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
      (linearChartCoordinate I z hz)) = 1
    rw [eval₂_linearChartCoordinate_eq_fraction I z hz ell hell']
    have hself := AllCharacteristics.GradedChart.normalized_self (grading I) hz
    change Away.mk (grading I) hz 1 z (by simpa only [one_smul] using hz) = 1 at hself
    have hfrac : Away.mk (grading I) hz 1
        (Ideal.Quotient.mk I.toIdeal ell)
        (polynomial_class_mem_grading I ell hell') = 1 := by
      simpa only [hellz'] using hself
    rw [hfrac, map_one]
  · intro q d hq hI
    change eval₂Hom (algebraMap K Γ(Z, ⊤)) x q = 0
    rw [he, RingHom.comp_apply]
    rw [show eval₂Hom _ (linearChartCoordinate I z hz) q = 0 from
      eval₂_linearChartCoordinate_eq_zero I z hz q hq hI, map_zero]

/-- A normalized projective-chart presentation of a finite closed subscheme.

Unlike the coordinate-only formulation, this retains the chart morphism and
its equality with the original immersion after affine reconstruction.  It is
therefore suitable for constructions where a complete intersection must
contain this particular finite subscheme. -/
theorem finite_projective_closed_subscheme_normalized_chart
    (I : HomogeneousIdeal (homogeneousSubmodule σ K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    ∃ (z : CoordinateRing I) (hz : z ∈ grading I 1)
      (g : Away (grading I) z →+* Γ(Z, ⊤)), Function.Surjective g ∧
      g.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
        algebraMap K Γ(Z, ⊤) ∧
      Spec.map (CommRingCat.ofHom g) ≫
        Proj.awayι (grading I) z hz (by decide : 0 < 1) = Z.isoSpec.inv ≫ i ∧
      ∃ (ell : MvPolynomial σ K) (hell : ell.IsHomogeneous 1),
        Ideal.Quotient.mk I.toIdeal ell = z ∧
      ∃ (x : σ → Γ(Z, ⊤)),
        (∀ j, x j = g (linearChartCoordinate I z hz j)) ∧
        Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
        ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 ∧
        ∃ (he : ∀ (q : MvPolynomial σ K), q ∈ I.toIdeal →
          q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0),
        ∃ hzOne : (Ideal.Quotient.lift I.toIdeal
          (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) he) z = 1,
          linearNormalizedPointAt I x he z hz hzOne = Z.isoSpec.inv ≫ i := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  obtain ⟨z, hz, g, hgs, hbase, hdiag⟩ := finite_projective_closed_subscheme_chart I i
  have hz' := hz
  obtain ⟨ell, hell, hellz⟩ := hz'
  have hellz' : Ideal.Quotient.mk I.toIdeal ell = z := hellz
  let x : σ → Γ(Z, ⊤) := fun j ↦ g (linearChartCoordinate I z hz j)
  have heval : eval₂Hom (algebraMap K Γ(Z, ⊤)) x =
      g.comp (eval₂Hom
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
        (linearChartCoordinate I z hz)) := by
    apply RingHom.ext
    intro q
    change q.eval₂ (algebraMap K Γ(Z, ⊤)) x = g (q.eval₂ _ _)
    rw [hom_eval₂, hbase]
  have hxsurj : Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) := by
    rw [heval]
    exact hgs.comp (eval₂_linearChartCoordinate_surjective I z hz)
  have hxell : ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1 := by
    change eval₂Hom (algebraMap K Γ(Z, ⊤)) x ell = 1
    rw [heval, RingHom.comp_apply]
    change g (ell.eval₂
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
      (linearChartCoordinate I z hz)) = 1
    rw [eval₂_linearChartCoordinate_eq_fraction I z hz ell hell]
    have hself := AllCharacteristics.GradedChart.normalized_self (grading I) hz
    change Away.mk (grading I) hz 1 z (by simpa only [one_smul] using hz) = 1 at hself
    have hfrac : Away.mk (grading I) hz 1 (Ideal.Quotient.mk I.toIdeal ell)
        (polynomial_class_mem_grading I ell hell) = 1 := by
      simpa only [hellz'] using hself
    rw [hfrac, map_one]
  have he : ∀ (q : MvPolynomial σ K), q ∈ I.toIdeal →
      q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 := by
    classical
    intro q hq
    rw [← DirectSum.sum_support_decompose
      (MvPolynomial.homogeneousSubmodule σ K) q, MvPolynomial.eval₂_sum]
    apply Finset.sum_eq_zero
    intro n _
    let qn : MvPolynomial σ K :=
      DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K) q n
    have hqn : qn.IsHomogeneous n := by
      exact (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K) q n).2
    have hqnI : qn ∈ I.toIdeal := I.isHomogeneous n hq
    change eval₂Hom (algebraMap K Γ(Z, ⊤)) x
      qn = 0
    rw [heval, RingHom.comp_apply]
    rw [show eval₂Hom _ (linearChartCoordinate I z hz)
        qn = 0 from
      eval₂_linearChartCoordinate_eq_zero I z hz qn hqn hqnI, map_zero]
  let he' : ∀ q ∈ I.toIdeal, q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0 :=
    fun q hq ↦ he q hq
  have hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) he') z = 1 := by
    rw [← hellz']
    exact hxell
  have hg : g = linearNormalizedPointChartMapAt I x he' z hz hzOne :=
    linearNormalizedPointChartMapAt_eq_of_base_and_coordinates I x he' z hz hzOne g
      hbase (fun _ => rfl)
  refine ⟨z, hz, g, hgs, hbase, hdiag, ell, hell, hellz', x, fun _ => rfl,
    hxsurj, hxell, he, hzOne, ?_⟩
  change Spec.map (CommRingCat.ofHom
    (linearNormalizedPointChartMapAt I x he' z hz hzOne)) ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1) = _
  rw [← hg]
  exact hdiag

/-- A finite closed subscheme of a homogeneous projective scheme admits one
normalized chart in the ambient projective space which both recovers the
original immersion and makes every equation of the homogeneous ideal vanish.
This retains the factorization data needed by universal-incidence arguments. -/
theorem finite_projective_closed_subscheme_normalized_ambient_chart
    (I : HomogeneousIdeal (homogeneousSubmodule σ K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I)
    [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    ∃ (ell : MvPolynomial σ K) (hell : ell.IsHomogeneous 1)
      (x : σ → Γ(Z, ⊤))
      (he₀ : ∀ q ∈ (⊥ : HomogeneousIdeal
        (homogeneousSubmodule σ K)).toIdeal,
        (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) q = 0)
      (hellOne : (Ideal.Quotient.lift
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)).toIdeal
        (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) he₀)
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)).toIdeal ell) = 1),
      Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) ∧
      (∀ q ∈ I.toIdeal,
        q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0) ∧
      linearNormalizedPointAt
          (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
          x he₀
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)).toIdeal ell)
          (polynomial_class_mem_grading
            (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) ell hell)
          hellOne ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) =
        Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  obtain ⟨z, hz, g, hgs, hbase, hdiag, ell, hell, hellz, x, hx,
    hxsurj, hxell, heI, hzOneI, hpoint⟩ :=
    finite_projective_closed_subscheme_normalized_chart I i
  let I₀ : HomogeneousIdeal (homogeneousSubmodule σ K) := ⊥
  let he₀ : ∀ q ∈ I₀.toIdeal,
      (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) q = 0 := by
    intro q hq
    have hq0 : q = 0 := Ideal.mem_bot.mp hq
    subst q
    exact map_zero _
  let z₀ : CoordinateRing I₀ := Ideal.Quotient.mk I₀.toIdeal ell
  have hz₀ : z₀ ∈ grading I₀ 1 :=
    polynomial_class_mem_grading I₀ ell hell
  have hz₀One : (Ideal.Quotient.lift I₀.toIdeal
      (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) he₀) z₀ = 1 := by
    change ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1
    exact hxell
  let hI₀I : I₀.toIdeal ≤ I.toIdeal := bot_le
  have hzIOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) heI)
        (gradedQuotientMap I₀ I hI₀I z₀) = 1 := by
    change ell.eval₂ (algebraMap K Γ(Z, ⊤)) x = 1
    exact hxell
  have hfactor :
      linearNormalizedPointAt I x heI
          (gradedQuotientMap I₀ I hI₀I z₀)
          ((gradedQuotientMap I₀ I hI₀I).map_mem hz₀) hzIOne ≫
        schemeQuotientMap I₀ I hI₀I =
      linearNormalizedPointAt I₀ x he₀ z₀ hz₀ hz₀One := by
    exact linearNormalizedPointAt_comp_schemeQuotientMap
      I₀ I hI₀I x he₀ heI z₀ hz₀ hz₀One hzIOne
  have hzz : gradedQuotientMap I₀ I hI₀I z₀ = z := by
    change Ideal.Quotient.mk I.toIdeal ell = z
    exact hellz
  have hpointI :
      linearNormalizedPointAt I x heI
          (gradedQuotientMap I₀ I hI₀I z₀)
          ((gradedQuotientMap I₀ I hI₀I).map_mem hz₀) hzIOne =
        Z.isoSpec.inv ≫ i := by
    simpa only [hzz] using hpoint
  refine ⟨ell, hell, x, he₀, hz₀One, hxsurj, heI, ?_⟩
  calc
    linearNormalizedPointAt I₀ x he₀ z₀ hz₀ hz₀One ≫
        quotientProjMap I₀ =
      (linearNormalizedPointAt I x heI
          (gradedQuotientMap I₀ I hI₀I z₀)
          ((gradedQuotientMap I₀ I hI₀I).map_mem hz₀) hzIOne ≫
        schemeQuotientMap I₀ I hI₀I) ≫ quotientProjMap I₀ := by
          exact congrArg (fun t ↦ t ≫ quotientProjMap I₀) hfactor.symm
    _ = linearNormalizedPointAt I x heI
          (gradedQuotientMap I₀ I hI₀I z₀)
          ((gradedQuotientMap I₀ I hI₀I).map_mem hz₀) hzIOne ≫
        quotientProjMap I := by
          rw [Category.assoc, schemeQuotientMap_comp_quotientProjMap]
    _ = (Z.isoSpec.inv ≫ i) ≫ quotientProjMap I := by
          exact congrArg (fun t ↦ t ≫ quotientProjMap I) hpointI
    _ = _ := by rfl

end

end PfaffianDescent

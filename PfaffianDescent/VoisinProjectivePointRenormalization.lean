import PfaffianDescent.VoisinProjectiveVectorSchemePoint
import PfaffianDescent.VoisinNormalizedPointAtCompatibility

/-!
# Renormalizing a projective point

Changing from a standard coordinate normalization to any nonvanishing linear
form rescales the coordinate vector and leaves the resulting projective
morphism unchanged.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A point normalized in a standard coordinate chart may be renormalized by
any ground-field linear form which is nonzero on its extension-field
coordinates.  The resulting projective morphism is unchanged. -/
theorem linearNormalizedPoint_exists_rescaling_in_linearChart
    {K A : Type u} [Field K] [Field A] [Algebra K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (y : Fin 4 → A) (j : Fin 4)
    (hyj : y j = 1)
    (hey : ∀ p ∈ I.toIdeal,
      p.eval₂ (algebraMap K A) y = 0)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (hellne : ell.eval₂ (algebraMap K A) y ≠ 0) :
    ∃ (v : Fin 4 → A)
      (_ : v = (ell.eval₂ (algebraMap K A) y)⁻¹ • y)
      (hvone : ell.eval₂ (algebraMap K A) v = 1)
      (hvzero : ∀ p ∈ I.toIdeal,
        p.eval₂ (algebraMap K A) v = 0),
      linearNormalizedPoint I y (X j) (isHomogeneous_X K j)
          (by simpa using hyj) hey =
        linearNormalizedPoint I v ell hell hvone hvzero := by
  let a : A := ell.eval₂ (algebraMap K A) y
  let v : Fin 4 → A := a⁻¹ • y
  have hvj : v j ≠ 0 := by
    simp only [v, Pi.smul_apply, smul_eq_mul, hyj, mul_one]
    exact inv_ne_zero hellne
  have hvone : ell.eval₂ (algebraMap K A) v = 1 := by
    change ell.eval₂ (algebraMap K A) (a⁻¹ • y) = 1
    rw [AllCharacteristics.eval₂_homogeneous_smul ell hell]
    simpa only [pow_one, a] using inv_mul_cancel₀ hellne
  have hvzero : ∀ p ∈ I.toIdeal,
      p.eval₂ (algebraMap K A) v = 0 := by
    intro p hp
    change (eval₂Hom (algebraMap K A) (a⁻¹ • y)) p = 0
    rw [← MvPolynomial.sum_homogeneousComponent p, map_sum]
    apply Finset.sum_eq_zero
    intro d hd
    have hcomp : homogeneousComponent d p ∈ I.toIdeal := by
      rw [← decomposition.decompose'_apply]
      exact I.isHomogeneous d hp
    change (homogeneousComponent d p).eval₂ (algebraMap K A)
      (a⁻¹ • y) = 0
    rw [AllCharacteristics.eval₂_homogeneous_smul
      (homogeneousComponent d p) (homogeneousComponent_isHomogeneous d p)]
    rw [hey _ hcomp, mul_zero]
  let uy : Aˣ := 1
  let uv : Aˣ := Units.mk0 (v j) hvj
  have hyX : (X j).eval₂ (algebraMap K A) y = 1 := by
    simpa using hyj
  obtain ⟨gy, hgy, hpy⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint
      I y (X j) (isHomogeneous_X K j) hyX hey j uy
        (by simp [uy, hyj])
  obtain ⟨gv, hgv, hpv⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint
      I v ell hell hvone hvzero j uv rfl
  have chartHom_base (g : ChartRing I j →+* A)
      {x : Fin 4 → A} {ell' : MvPolynomial (Fin 4) K}
      {hell' : ell'.IsHomogeneous 1}
      {hxell : ell'.eval₂ (algebraMap K A) x = 1}
      {he : ∀ p ∈ I.toIdeal,
        p.eval₂ (algebraMap K A) x = 0}
      (hpoint : Spec.map (CommRingCat.ofHom g) ≫ chartι I j =
        linearNormalizedPoint I x ell' hell' hxell he) :
      g.comp (chartBaseMap I j) = algebraMap K A := by
    have hs : Spec.map (CommRingCat.ofHom
        (g.comp (chartBaseMap I j))) =
        Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
      calc
        _ = Spec.map (CommRingCat.ofHom g) ≫
            Spec.map (CommRingCat.ofHom (chartBaseMap I j)) := by
          rw [← Spec.map_comp]
          rfl
        _ = (Spec.map (CommRingCat.ofHom g) ≫ chartι I j) ≫
            toBase I := by rw [Category.assoc, chartι_toBase]
        _ = linearNormalizedPoint I x ell' hell' hxell he ≫
            toBase I := by rw [hpoint]
        _ = Spec.map (CommRingCat.ofHom (algebraMap K A)) :=
          linearNormalizedPoint_toBase I x ell' hell' hxell he
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  have hgybase : gy.comp (chartBaseMap I j) = algebraMap K A :=
    chartHom_base gy hpy
  have hgvbase : gv.comp (chartBaseMap I j) = algebraMap K A :=
    chartHom_base gv hpv
  have hmaps : gy = gv := by
    apply RingHom.ext
    intro b
    obtain ⟨q, hq⟩ := eval₂_chartCoordinate_surjective I j b
    rw [← hq]
    change gy (q.eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
      gv (q.eval₂ (chartBaseMap I j) (chartCoordinate I j))
    rw [MvPolynomial.hom_eval₂, MvPolynomial.hom_eval₂]
    rw [hgybase, hgvbase]
    congr 1
    funext k
    rw [hgy k, hgv k]
    simp [uy, uv, v, a, hyj, hellne, Units.val_inv_eq_inv_val]
  refine ⟨v, rfl, hvone, hvzero, ?_⟩
  calc
    linearNormalizedPoint I y (X j) (isHomogeneous_X K j) hyX hey =
        Spec.map (CommRingCat.ofHom gy) ≫ chartι I j := hpy.symm
    _ = Spec.map (CommRingCat.ofHom gv) ≫ chartι I j := by rw [hmaps]
    _ = linearNormalizedPoint I v ell hell hvone hvzero := hpv

/-- Specialized form of projective renormalization in which the resulting
vector is the canonical normalization by a ground-field linear form after
extension of scalars. -/
theorem linearNormalizedPoint_eq_normalizedVectorInLinearChart
    {K A : Type u} [Field K] [Field A] [Algebra K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (y : Fin 4 → A) (j : Fin 4)
    (hyj : y j = 1)
    (hey : ∀ p ∈ I.toIdeal,
      p.eval₂ (algebraMap K A) y = 0)
    (c : Fin 4 → K)
    (hc : (homogeneousLinearForm
      (fun k => algebraMap K A (c k))).eval y ≠ 0) :
    let cA : Fin 4 → A := fun k => algebraMap K A (c k)
    let v := normalizedVectorInLinearChart cA y
    ∃ (hvone : (homogeneousLinearForm c).eval₂
        (algebraMap K A) v = 1)
      (hvzero : ∀ p ∈ I.toIdeal,
        p.eval₂ (algebraMap K A) v = 0),
      linearNormalizedPoint I y (X j) (isHomogeneous_X K j)
          (by simpa using hyj) hey =
        linearNormalizedPoint I v (homogeneousLinearForm c)
          (homogeneousLinearForm_isHomogeneous c) hvone hvzero := by
  dsimp only
  let cA : Fin 4 → A := fun k => algebraMap K A (c k)
  let v := normalizedVectorInLinearChart cA y
  have hellne : (homogeneousLinearForm c).eval₂
      (algebraMap K A) y ≠ 0 := by
    simpa only [homogeneousLinearForm, MvPolynomial.eval_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X] using hc
  obtain ⟨w, hw, hwone, hwzero, hpoint⟩ :=
    linearNormalizedPoint_exists_rescaling_in_linearChart I y j hyj hey
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
      hellne
  have hwv : w = v := by
    rw [hw]
    funext k
    simp only [v, normalizedVectorInLinearChart, Pi.smul_apply,
      smul_eq_mul]
    congr 1
    simp only [cA, homogeneousLinearForm, MvPolynomial.eval_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  clear hw
  subst w
  exact ⟨hwone, hwzero, hpoint⟩

/-- The standard-coordinate presentation of a projective point belongs to
every ground-field linear basic open whose defining form evaluates nonzero
on its extension-field coordinate vector. -/
theorem linearNormalizedPoint_mem_basicOpen_of_eval₂_ne_zero
    {K A : Type u} [Field K] [Field A] [Algebra K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (y : Fin 4 → A) (j : Fin 4)
    (hyj : y j = 1)
    (hey : ∀ p ∈ I.toIdeal,
      p.eval₂ (algebraMap K A) y = 0)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (hellne : ell.eval₂ (algebraMap K A) y ≠ 0) :
    linearNormalizedPoint I y (X j) (isHomogeneous_X K j)
        (by simpa using hyj) hey (IsLocalRing.closedPoint A) ∈
      Proj.basicOpen (grading I) (Ideal.Quotient.mk I.toIdeal ell) := by
  obtain ⟨v, _, hvone, hvzero, hpoint⟩ :=
    linearNormalizedPoint_exists_rescaling_in_linearChart
      I y j hyj hey ell hell hellne
  rw [hpoint]
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal ell
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  rw [← Proj.opensRange_awayι (grading I) z hz (by decide : 0 < 1)]
  unfold linearNormalizedPoint
  exact ⟨_, rfl⟩

theorem linearNormalizedPoint_eq_projectiveVectorSchemePointInLinearChart
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (y : Fin 4 → K) (j : Fin 4)
    (hyj : y j = 1)
    (hey : ∀ p ∈ I.toIdeal, p.eval y = 0)
    (c : Fin 4 → K)
    (hc : (homogeneousLinearForm c).eval y ≠ 0) :
    linearNormalizedPoint I y (X j) (isHomogeneous_X K j)
        (by simpa using hyj) (by simpa using hey) =
      projectiveVectorSchemePointInLinearChart I c y hey hc := by
  let v := normalizedVectorInLinearChart c y
  have hvj : v j ≠ 0 := by
    dsimp only [v, normalizedVectorInLinearChart]
    simp only [Pi.smul_apply, smul_eq_mul, hyj, mul_one]
    exact inv_ne_zero hc
  let uy : Kˣ := 1
  let uv : Kˣ := Units.mk0 (v j) hvj
  have hyX : (X j).eval y = 1 := by simpa using hyj
  have hey' : ∀ p ∈ I.toIdeal,
      p.eval₂ (algebraMap K K) y = 0 := by
    intro p hp
    simpa using hey p hp
  have hvzero : ∀ p ∈ I.toIdeal, p.eval v = 0 :=
    normalizedVectorInLinearChart_zero I c y hey
  have hvzero' : ∀ p ∈ I.toIdeal,
      p.eval₂ (algebraMap K K) v = 0 := by
    intro p hp
    simpa using hvzero p hp
  have hvone := normalizedVectorInLinearChart_eval_one c y hc
  obtain ⟨gy, hgy, hpy⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint
      I y (X j) (isHomogeneous_X K j) hyX hey' j uy (by simp [uy, hyj])
  obtain ⟨gv, hgv, hpv⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint
      I v (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
      (by simpa using hvone) hvzero' j uv rfl
  have chartHom_base (g : ChartRing I j →+* K)
      {x : Fin 4 → K} {ell : MvPolynomial (Fin 4) K}
      {hell : ell.IsHomogeneous 1}
      {hxell : ell.eval₂ (algebraMap K K) x = 1}
      {he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K K) x = 0}
      (hpoint : Spec.map (CommRingCat.ofHom g) ≫ chartι I j =
        linearNormalizedPoint I x ell hell hxell he) :
      g.comp (chartBaseMap I j) = RingHom.id K := by
    have hs : Spec.map (CommRingCat.ofHom (g.comp (chartBaseMap I j))) =
        Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
      calc
        _ = Spec.map (CommRingCat.ofHom g) ≫
            Spec.map (CommRingCat.ofHom (chartBaseMap I j)) := by
          rw [← Spec.map_comp]
          rfl
        _ = (Spec.map (CommRingCat.ofHom g) ≫ chartι I j) ≫
            toBase I := by rw [Category.assoc, chartι_toBase]
        _ = linearNormalizedPoint I x ell hell hxell he ≫ toBase I := by
          rw [hpoint]
        _ = Spec.map (CommRingCat.ofHom (algebraMap K K)) :=
          linearNormalizedPoint_toBase I x ell hell hxell he
        _ = _ := by
          congr 2
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  have hgybase : gy.comp (chartBaseMap I j) = RingHom.id K :=
    chartHom_base gy hpy
  have hgvbase : gv.comp (chartBaseMap I j) = RingHom.id K :=
    chartHom_base gv hpv
  have hmaps : gy = gv := by
    apply RingHom.ext
    intro a
    obtain ⟨q, hq⟩ := eval₂_chartCoordinate_surjective I j a
    rw [← hq]
    change gy (q.eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
      gv (q.eval₂ (chartBaseMap I j) (chartCoordinate I j))
    rw [MvPolynomial.hom_eval₂, MvPolynomial.hom_eval₂]
    rw [hgybase, hgvbase]
    congr 1
    funext k
    rw [hgy k, hgv k]
    simp [uy, uv, v, normalizedVectorInLinearChart, hyj, hc,
      Units.val_inv_eq_inv_val]
  calc
    linearNormalizedPoint I y (X j) (isHomogeneous_X K j) hyX hey' =
        Spec.map (CommRingCat.ofHom gy) ≫ chartι I j := hpy.symm
    _ = Spec.map (CommRingCat.ofHom gv) ≫ chartι I j := by rw [hmaps]
    _ = linearNormalizedPoint I v (homogeneousLinearForm c)
        (homogeneousLinearForm_isHomogeneous c) (by simpa using hvone)
          hvzero' := hpv
    _ = projectiveVectorSchemePointInLinearChart I c y hey hc := by
      symm
      unfold projectiveVectorSchemePointInLinearChart
        projectiveLinearNormalizedVectorSchemePoint
      simpa only [v] using
        (linearNormalizedPointAt_mk_eq_linearNormalizedPoint
          I v hvzero' (homogeneousLinearForm c)
            (homogeneousLinearForm_isHomogeneous c) (by simpa using hvone))

end PfaffianDescent

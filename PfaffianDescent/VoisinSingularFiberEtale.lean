import PfaffianDescent.VoisinJacobianUniversalFamily
import PfaffianDescent.ProjectiveSpaceRationalOpen

/-!
# From an empty singular fiber to étaleness

The common-source universal family detects simultaneous vanishing of the two
fixed cubics, the moving cubic, and all four projective Jacobian minors.  This
file converts emptiness of that projective singular scheme into invertibility
of every normalized chart Jacobian and hence into étaleness of the selected
three-cubic intersection.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics HomogeneousProjective

universe u

section

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- If the projective scheme cut out by three cubics and all four maximal
Jacobian minors is empty, every normalized chart Jacobian is a unit. -/
theorem tripleCompleteIntersectionChartJacobian_isUnit_of_isEmpty_singularScheme
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3)
    (hempty : IsEmpty (scheme
      (tripleCompleteIntersectionSingularHomogeneousIdeal
        p q r hp hq hr))) :
    ∀ j : Fin 4,
      IsUnit (tripleCompleteIntersectionChartJacobian
        p q r hp hq hr j) := by
  intro j
  by_contra hunit
  let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let A := ChartRing J j
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span ({tripleCompleteIntersectionChartJacobian
      p q r hp hq hr j} : Set A))
    (Ideal.span_singleton_ne_top hunit)
  let Q : MaximalSpectrum A := ⟨M, hM⟩
  letI : Algebra K A := (chartBaseMap J j).toAlgebra
  let e : MvPolynomial (Fin 4) K →ₐ[K] A :=
    MvPolynomial.eval₂AlgHom K (chartCoordinate J j)
  let L := Q.asIdeal.ResidueField
  let x : Fin 4 → L :=
    tripleCompleteIntersectionResidueEvaluation e Q
  have hxj : x j ≠ 0 := by
    simpa only [x, e] using
      tripleCompleteIntersectionResidueEvaluation_chartCoordinate_ne_zero J j Q
  have hpJ : p ∈ J.toIdeal := by
    dsimp [J]
    rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
    exact Ideal.subset_span (by simp)
  have hqJ : q ∈ J.toIdeal := by
    dsimp [J]
    rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
    exact Ideal.subset_span (by simp)
  have hrJ : r ∈ J.toIdeal := by
    dsimp [J]
    rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
    exact Ideal.subset_span (by simp)
  have hep : e p = 0 := by
    change p.eval₂ (chartBaseMap J j) (chartCoordinate J j) = 0
    exact eval₂_chartCoordinate_eq_zero_of_mem J j p hpJ
  have heq : e q = 0 := by
    change q.eval₂ (chartBaseMap J j) (chartCoordinate J j) = 0
    exact eval₂_chartCoordinate_eq_zero_of_mem J j q hqJ
  have her : e r = 0 := by
    change r.eval₂ (chartBaseMap J j) (chartCoordinate J j) = 0
    exact eval₂_chartCoordinate_eq_zero_of_mem J j r hrJ
  have hpx : (p.map (algebraMap K L)).eval x = 0 := by
    change (MvPolynomial.eval₂Hom (RingHom.id Q.asIdeal.ResidueField) x)
      (p.map (algebraMap K Q.asIdeal.ResidueField)) = 0
    rw [← tripleCompleteIntersectionResidueEvaluation_map_eval e Q p,
      hep, map_zero]
  have hqx : (q.map (algebraMap K L)).eval x = 0 := by
    change (MvPolynomial.eval₂Hom (RingHom.id Q.asIdeal.ResidueField) x)
      (q.map (algebraMap K Q.asIdeal.ResidueField)) = 0
    rw [← tripleCompleteIntersectionResidueEvaluation_map_eval e Q q,
      heq, map_zero]
  have hrx : (r.map (algebraMap K L)).eval x = 0 := by
    change (MvPolynomial.eval₂Hom (RingHom.id Q.asIdeal.ResidueField) x)
      (r.map (algebraMap K Q.asIdeal.ResidueField)) = 0
    rw [← tripleCompleteIntersectionResidueEvaluation_map_eval e Q r,
      her, map_zero]
  have hjacM : tripleCompleteIntersectionChartJacobian
      p q r hp hq hr j ∈ M :=
    hle (Ideal.subset_span (Set.mem_singleton _))
  have hjacZero : algebraMap A L
      (tripleCompleteIntersectionChartJacobian p q r hp hq hr j) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hjacM
  have hjMapped :
      ((tripleCompleteIntersectionChartJacobianPolynomial p q r j).map
        (algebraMap K L)).eval x = 0 := by
    calc
      _ = algebraMap A L
          (e (tripleCompleteIntersectionChartJacobianPolynomial p q r j)) :=
        (tripleCompleteIntersectionResidueEvaluation_map_eval e Q
          (tripleCompleteIntersectionChartJacobianPolynomial p q r j)).symm
      _ = algebraMap A L
          (tripleCompleteIntersectionChartJacobian p q r hp hq hr j) := by
        rfl
      _ = 0 := hjacZero
  have hj :
      (tripleCompleteIntersectionChartJacobianPolynomial
        (p.map (algebraMap K L)) (q.map (algebraMap K L))
        (r.map (algebraMap K L)) j).eval x = 0 := by
    rw [← tripleCompleteIntersectionChartJacobianPolynomial_map
      (algebraMap K L) p q r hp hq hr j]
    exact hjMapped
  have hall :=
    all_tripleCompleteIntersectionChartJacobianPolynomial_eval_eq_zero_of_one
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L)) x
      (hp.map (algebraMap K L)) (hq.map (algebraMap K L))
      (hr.map (algebraMap K L)) hpx hqx hrx j hxj hj
  let I := tripleCompleteIntersectionSingularHomogeneousIdeal p q r hp hq hr
  have heval : ∀ s : MvPolynomial (Fin 4) K,
      s ∈ I.toIdeal → s.eval₂ (algebraMap K L) x = 0 := by
    intro s hs
    have hker : I.toIdeal ≤
        RingHom.ker (MvPolynomial.eval₂Hom (algebraMap K L) x) := by
      dsimp [I]
      rw [tripleCompleteIntersectionSingularIdeal]
      apply Ideal.span_le.mpr
      intro a ha
      rcases ha with ha | ha
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · simpa [MvPolynomial.eval₂_map] using hpx
        · simpa [MvPolynomial.eval₂_map] using hqx
        · simpa [MvPolynomial.eval₂_map] using hrx
      · obtain ⟨k, rfl⟩ := ha
        change MvPolynomial.eval₂ (algebraMap K L) x
          (tripleCompleteIntersectionChartJacobianPolynomial p q r k) = 0
        rw [MvPolynomial.eval₂_eq_eval_map,
          tripleCompleteIntersectionChartJacobianPolynomial_map
            (algebraMap K L) p q r hp hq hr k]
        exact hall k
    exact hker hs
  have hx : x ≠ 0 := by
    intro hzero
    exact hxj (congrFun hzero j)
  obtain ⟨t, _⟩ := point_of_coordinates I (algebraMap K L) x hx heval
  exact hempty.false (t (IsLocalRing.closedPoint L))

/-- Empty simultaneous singular scheme gives the étaleness conclusion used
by Voisin's selected third-cubic construction. -/
theorem etale_tripleCompleteIntersection_toBase_of_isEmpty_singularScheme
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3)
    (hempty : IsEmpty (scheme
      (tripleCompleteIntersectionSingularHomogeneousIdeal
        p q r hp hq hr))) :
    Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) :=
  etale_tripleCompleteIntersection_toBase_of_chartJacobian_isUnit
    p q r hp hq hr
      (tripleCompleteIntersectionChartJacobian_isUnit_of_isEmpty_singularScheme
        p q r hp hq hr hempty)

/-- An empty simultaneous-singularity fiber of the universal family makes
the corresponding specialized three-cubic intersection étale. -/
theorem
    etale_tripleCompleteIntersection_toBase_of_isEmpty_universalSingularChartFiber
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hempty : IsEmpty (scheme
      (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
        p q hp hq v i g))) :
    Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
      (q.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
      (((tripleCompleteIntersectionUniversalCubic v).map
        (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g)
      (hp.map _)
      (hq.map _)
      ((tripleCompleteIntersectionUniversalCubic_isHomogeneous v).map _ |>.map g))) := by
  apply etale_tripleCompleteIntersection_toBase_of_isEmpty_singularScheme
  simpa only [tripleCompleteIntersectionUniversalSingularChartFiberIdeal] using hempty

/-- A field-valued parameter outside the global simultaneous-singularity
locus factors through a normalized parameter chart, and its specialized
three-cubic intersection is étale. -/
theorem
    exists_parameterChartHom_etale_of_fieldPoint_not_mem_singularParameterLocus
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (t : Spec (.of L) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom f))
    (hgood : t (IsLocalRing.closedPoint L) ∉
      tripleCompleteIntersectionUniversalSingularParameterLocus
        p q hp hq v) :
    ∃ (i : Fin n)
      (g : ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L),
      g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) = f ∧
      Spec.map (CommRingCat.ofHom g) ≫
        chartι (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin n) K)) i = t ∧
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (q.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (((tripleCompleteIntersectionUniversalCubic v).map
          (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g)
        (hp.map _)
        (hq.map _)
        ((tripleCompleteIntersectionUniversalCubic_isHomogeneous v).map _ |>.map g))) := by
  obtain ⟨i, g, hgbase, hgt, hempty⟩ :=
    exists_parameterChartHom_empty_singularFiber_of_fieldPoint_not_mem_singularParameterLocus
      f p q hp hq v t ht hgood
  exact ⟨i, g, hgbase, hgt,
    etale_tripleCompleteIntersection_toBase_of_isEmpty_universalSingularChartFiber
      p q hp hq v i g hempty⟩

/-- Over an infinite ground field, properness of the universal singular-member
 locus supplies a normalized parameter-chart point whose specialized
projective singular fiber is empty. -/
theorem
    exists_groundField_parameterChartHom_empty_singularFiber_of_singularParameterLocus_ne_univ
    [Infinite K] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (hproper : tripleCompleteIntersectionUniversalSingularParameterLocus
      p q hp hq v ≠ Set.univ) :
    ∃ (i : Fin n)
      (g : ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* K),
      g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) =
          RingHom.id K ∧
      IsEmpty (scheme
        (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
          p q hp hq v i g)) := by
  classical
  let U : Scheme.Opens
      (projectiveLinearSystemParameters (K := K) (τ := Fin n)) :=
    ⟨tripleCompleteIntersectionUniversalNonsingularParameterLocus p q hp hq v,
      isOpen_tripleCompleteIntersectionUniversalNonsingularParameterLocus
        p q hp hq v⟩
  obtain ⟨x, hx⟩ :=
    (Set.ne_univ_iff_exists_notMem
      (tripleCompleteIntersectionUniversalSingularParameterLocus
        p q hp hq v)).mp hproper
  have hxU : x ∈ (U : Set
      (projectiveLinearSystemParameters (K := K) (τ := Fin n))) := by
    simpa [U,
      tripleCompleteIntersectionUniversalSingularParameterLocus,
      Set.mem_compl_iff] using hx
  obtain ⟨s, hs⟩ :=
    nonempty_open_projectiveSpace_has_rational_section U ⟨x, hxU⟩
  let t : Spec (.of K) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n) := s ≫ U.ι
  have ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
    change t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (𝟙 (CommRingCat.of K))
    rw [Spec.map_id]
    exact hs
  have hgood : t (IsLocalRing.closedPoint K) ∉
      tripleCompleteIntersectionUniversalSingularParameterLocus
        p q hp hq v := by
    change U.ι (s (IsLocalRing.closedPoint K)) ∉
      tripleCompleteIntersectionUniversalSingularParameterLocus
        p q hp hq v
    have hsU : U.ι (s (IsLocalRing.closedPoint K)) ∈ (U : Set
        (projectiveLinearSystemParameters (K := K) (τ := Fin n))) :=
      (s (IsLocalRing.closedPoint K)).property
    simpa [U,
      tripleCompleteIntersectionUniversalSingularParameterLocus,
      Set.mem_compl_iff] using hsU
  obtain ⟨i, g, hgbase, _hgt, hempty⟩ :=
    exists_parameterChartHom_empty_singularFiber_of_fieldPoint_not_mem_singularParameterLocus
      (RingHom.id K) p q hp hq v t ht hgood
  exact ⟨i, g, hgbase, hempty⟩

/-- The empty-fiber selector also gives the usual finite-etale conclusion. -/
theorem
    exists_groundField_parameterChartHom_etale_of_singularParameterLocus_ne_univ
    [Infinite K] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (hproper : tripleCompleteIntersectionUniversalSingularParameterLocus
      p q hp hq v ≠ Set.univ) :
    ∃ (i : Fin n)
      (g : ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* K),
      g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) =
          RingHom.id K ∧
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (q.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (((tripleCompleteIntersectionUniversalCubic v).map
          (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g)
        (hp.map _)
        (hq.map _)
        ((tripleCompleteIntersectionUniversalCubic_isHomogeneous v).map _ |>.map g))) := by
  obtain ⟨i, g, hgbase, hempty⟩ :=
    exists_groundField_parameterChartHom_empty_singularFiber_of_singularParameterLocus_ne_univ
      p q hp hq v hproper
  exact ⟨i, g, hgbase,
    etale_tripleCompleteIntersection_toBase_of_isEmpty_universalSingularChartFiber
      p q hp hq v i g hempty⟩

end

end PfaffianDescent

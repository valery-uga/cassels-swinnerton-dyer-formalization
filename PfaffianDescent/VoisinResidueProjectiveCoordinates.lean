import PfaffianDescent.VoisinProjectivePointScale
import PfaffianDescent.VoisinQuadraticEvaluationMatrixExtension
import PfaffianDescent.VoisinQuotientNormalizedAmbientChart
import AllCharacteristics.AmbientChartPresentation
import AllCharacteristics.AmbientProjectiveBaseChange
import AllCharacteristics.ProjectivePointCoordinates

/-!
# Coordinates of a projective point after a field extension

This file records the coordinate comparison needed for the residue-field
descent in Voisin's eight-point construction.  If a normalized projective
point over an extension field factors through a point over a smaller field,
then standard affine-chart coordinates of the smaller point map to the
corresponding independently rescaled homogeneous coordinates.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Once one homogeneous coordinate is normalized to one, the ambient
projective point reconstructed from the vector is independent of the
homogeneous ideal through which it was first presented. -/
theorem linearNormalizedPoint_quotientProjMap_eq_bot
    {K Q : Type u} [Field K] [Field Q] [Algebra K Q]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (y : Fin 4 → Q) (j : Fin 4)
    (hey : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K Q) y = 0)
    (hyj : y j = 1) :
    let hX : (X j).eval₂ (algebraMap K Q) y = 1 := by
      simpa only [MvPolynomial.eval₂_X] using hyj
    let he0 : ∀ p ∈ (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) K)).toIdeal,
        p.eval₂ (algebraMap K Q) y = 0 := by
      intro p hp
      rw [Ideal.mem_bot.mp hp]
      simp
    linearNormalizedPoint I y (X j) (isHomogeneous_X K j) hX hey ≫
        quotientProjMap I =
      linearNormalizedPoint
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
        y (X j) (isHomogeneous_X K j) hX he0 ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) := by
  dsimp only
  let hX : (X j).eval₂ (algebraMap K Q) y = 1 := by
    simpa only [MvPolynomial.eval₂_X] using hyj
  let he0 : ∀ p ∈ (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) K)).toIdeal,
      p.eval₂ (algebraMap K Q) y = 0 := by
    intro p hp
    rw [Ideal.mem_bot.mp hp]
    simp
  obtain ⟨gI, hgIPoint, hgICoordinates⟩ :=
    exists_ambientCoordinateChart_of_quotientNormalizedPointAt
      I y (X j) (isHomogeneous_X K j) hey hX j (by rw [hyj]; exact one_ne_zero)
  obtain ⟨g0, hg0Point, hg0Coordinates⟩ :=
    exists_ambientCoordinateChart_of_quotientNormalizedPointAt
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
      y (X j) (isHomogeneous_X K j) he0 hX j
        (by rw [hyj]; exact one_ne_zero)
  have chartBase (J : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) K))
      (heJ : ∀ p ∈ J.toIdeal, p.eval₂ (algebraMap K Q) y = 0)
      (g : Away (homogeneousSubmodule (Fin 4) K) (X j) →+* Q)
      (hg : Spec.map (CommRingCat.ofHom g) ≫
          Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
            (isHomogeneous_X K j) (by decide : 0 < 1) =
        linearNormalizedPointAt J y heJ
          (Ideal.Quotient.mk J.toIdeal (X j))
          (polynomial_class_mem_grading J (X j) (isHomogeneous_X K j)) hX ≫
          quotientProjMap J) :
      g.comp (AllCharacteristics.GradedChart.baseMap
        (homogeneousSubmodule (Fin 4) K) (z := X j)) = algebraMap K Q := by
    apply RingHom.ext
    have hs : Spec.map (CommRingCat.ofHom
        (g.comp (AllCharacteristics.GradedChart.baseMap
          (homogeneousSubmodule (Fin 4) K) (z := X j)))) =
        Spec.map (CommRingCat.ofHom (algebraMap K Q)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      calc
        Spec.map (CommRingCat.ofHom g) ≫
            Spec.map (CommRingCat.ofHom
              (AllCharacteristics.GradedChart.baseMap
                (homogeneousSubmodule (Fin 4) K) (z := X j))) =
          (Spec.map (CommRingCat.ofHom g) ≫
            Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
              (isHomogeneous_X K j) (by decide : 0 < 1)) ≫
            ambientToBase := by
              rw [Category.assoc,
                AllCharacteristics.HomogeneousProjective.ambientCoordinateChart_toBase]
        _ = (linearNormalizedPointAt J y heJ
              (Ideal.Quotient.mk J.toIdeal (X j))
              (polynomial_class_mem_grading J (X j)
                (isHomogeneous_X K j)) hX ≫ quotientProjMap J) ≫
            ambientToBase := congrArg (fun k => k ≫ ambientToBase) hg
        _ = linearNormalizedPointAt J y heJ
              (Ideal.Quotient.mk J.toIdeal (X j))
              (polynomial_class_mem_grading J (X j)
                (isHomogeneous_X K j)) hX ≫ toBase J := by
              rw [Category.assoc, quotientProjMap_toBase]
        _ = Spec.map (CommRingCat.ofHom (algebraMap K Q)) :=
          linearNormalizedPointAt_toBase J y heJ
            (Ideal.Quotient.mk J.toIdeal (X j))
            (polynomial_class_mem_grading J (X j)
              (isHomogeneous_X K j)) hX
    intro r
    exact RingHom.congr_fun
      (congrArg CommRingCat.Hom.hom (Spec.map_injective hs)) r
  have hbaseI := chartBase I hey gI hgIPoint
  have hbase0 := chartBase
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) he0 g0 hg0Point
  have hg : gI = g0 := by
    apply DFunLike.ext gI g0
    intro z
    obtain ⟨p, hp⟩ :=
      AllCharacteristics.HomogeneousProjective.ambientChartEvaluation_surjective
        (R := K) (σ := Fin 4) j z
    rw [← hp]
    dsimp only [AllCharacteristics.HomogeneousProjective.ambientChartEvaluation]
    change gI (p.eval₂
        (AllCharacteristics.GradedChart.baseMap
          (homogeneousSubmodule (Fin 4) K) (z := X j))
        (AllCharacteristics.HomogeneousProjective.ambientChartCoordinate j)) =
      g0 (p.eval₂
        (AllCharacteristics.GradedChart.baseMap
          (homogeneousSubmodule (Fin 4) K) (z := X j))
        (AllCharacteristics.HomogeneousProjective.ambientChartCoordinate j))
    rw [MvPolynomial.hom_eval₂, MvPolynomial.hom_eval₂, hbaseI, hbase0]
    congr 1
    funext k
    change gI (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
        (X k) (isHomogeneous_X K k)) =
      g0 (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
        (X k) (isHomogeneous_X K k))
    rw [hgICoordinates k, hg0Coordinates k]
  rw [← linearNormalizedPointAt_mk_eq_linearNormalizedPoint I y hey
      (X j) (isHomogeneous_X K j) hX,
    ← linearNormalizedPointAt_mk_eq_linearNormalizedPoint
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) y he0
      (X j) (isHomogeneous_X K j) hX]
  rw [← hgIPoint, ← hg0Point, hg]

/-- An ambient projective point which acquires a standard-chart presentation
after a field extension has normalized coordinates over the smaller field.
The descended coordinates reconstruct the original ambient morphism exactly. -/
theorem exists_coordinates_of_ambientPoint_chart_factorization
    {K Q L : Type u} [Field K] [Field Q] [Field L]
    [Algebra K Q] [Algebra K L]
    (e : Q →ₐ[K] L)
    (q : Spec (.of Q) ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (hq : q ≫ ambientToBase =
      Spec.map (CommRingCat.ofHom (algebraMap K Q)))
    (j : Fin 4)
    (gL : Away (homogeneousSubmodule (Fin 4) K) (X j) →+* L)
    (hfactor : Spec.map (CommRingCat.ofHom gL) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
          (isHomogeneous_X K j) (by decide : 0 < 1) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q) :
    ∃ y : Fin 4 → Q,
      y j = 1 ∧
      (∀ k, e (y k) = gL
        (AllCharacteristics.GradedChart.normalized
          (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
          (X k) (isHomogeneous_X K k))) ∧
      ∃ (he0 : ∀ p ∈ (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) K)).toIdeal,
          p.eval₂ (algebraMap K Q) y = 0)
        (hX : (X j).eval₂ (algebraMap K Q) y = 1),
        linearNormalizedPoint
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
            y (X j) (isHomogeneous_X K j) hX he0 ≫
          quotientProjMap
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) = q := by
  let chart := Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
    (isHomogeneous_X K j) (by decide : 0 < 1)
  have hj : q (IsLocalRing.closedPoint Q) ∈ Set.range chart := by
    have hs : (Spec.map (CommRingCat.ofHom e.toRingHom))
        (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint Q :=
      Subsingleton.elim _ _
    refine ⟨(Spec.map (CommRingCat.ofHom gL))
      (IsLocalRing.closedPoint L), ?_⟩
    calc
      chart ((Spec.map (CommRingCat.ofHom gL))
          (IsLocalRing.closedPoint L)) =
          (Spec.map (CommRingCat.ofHom gL) ≫ chart)
            (IsLocalRing.closedPoint L) := rfl
      _ = (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q)
          (IsLocalRing.closedPoint L) := by
        exact congrArg
          (fun f : Spec (.of L) ⟶
            Proj (homogeneousSubmodule (Fin 4) K) =>
              f (IsLocalRing.closedPoint L)) hfactor
      _ = q (IsLocalRing.closedPoint Q) := congrArg q hs
  have hrange : Set.range q ⊆ Set.range chart := by
    rintro _ ⟨s, rfl⟩
    have hs : s = IsLocalRing.closedPoint Q := Subsingleton.elim _ _
    simpa only [hs] using hj
  letI : IsOpenImmersion chart := by
    dsimp only [chart]
    unfold Proj.awayι
    exact IsOpenImmersion.comp _ _
  let qU := IsOpenImmersion.lift chart q hrange
  let gQ := (Spec.preimage qU).hom
  have hpQ : Spec.map (CommRingCat.ofHom gQ) ≫ chart = q := by
    change Spec.map (Spec.preimage qU) ≫ chart = q
    rw [Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  have hbaseQ : gQ.comp (AllCharacteristics.GradedChart.baseMap
      (homogeneousSubmodule (Fin 4) K) (z := X j)) = algebraMap K Q := by
    apply RingHom.ext
    intro r
    have hs : Spec.map (CommRingCat.ofHom
        (gQ.comp (AllCharacteristics.GradedChart.baseMap
          (homogeneousSubmodule (Fin 4) K) (z := X j)))) =
        Spec.map (CommRingCat.ofHom (algebraMap K Q)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      calc
        Spec.map (CommRingCat.ofHom gQ) ≫
            Spec.map (CommRingCat.ofHom
              (AllCharacteristics.GradedChart.baseMap
                (homogeneousSubmodule (Fin 4) K) (z := X j))) =
          (Spec.map (CommRingCat.ofHom gQ) ≫ chart) ≫ ambientToBase := by
            rw [Category.assoc,
              AllCharacteristics.HomogeneousProjective.ambientCoordinateChart_toBase]
        _ = q ≫ ambientToBase := congrArg (fun k => k ≫ ambientToBase) hpQ
        _ = Spec.map (CommRingCat.ofHom (algebraMap K Q)) := hq
    exact RingHom.congr_fun
      (congrArg CommRingCat.Hom.hom (Spec.map_injective hs)) r
  let y : Fin 4 → Q := fun k => gQ
    (AllCharacteristics.GradedChart.normalized
      (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
      (X k) (isHomogeneous_X K k))
  have hyj : y j = 1 := by
    dsimp only [y]
    change gQ (AllCharacteristics.HomogeneousProjective.ambientChartCoordinate j j) = 1
    rw [AllCharacteristics.HomogeneousProjective.ambientChartCoordinate_self, map_one]
  have hmaps : e.toRingHom.comp gQ = gL := by
    apply AllCharacteristics.HomogeneousProjective.ambientCoefficientChartMap_eq_of_projective_eq
      j
    calc
      Spec.map (CommRingCat.ofHom (e.toRingHom.comp gQ)) ≫ chart =
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫
            (Spec.map (CommRingCat.ofHom gQ) ≫ chart) := by
        rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q := by rw [hpQ]
      _ = Spec.map (CommRingCat.ofHom gL) ≫ chart := hfactor.symm
  let he0 : ∀ p ∈ (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) K)).toIdeal,
      p.eval₂ (algebraMap K Q) y = 0 := by
    intro p hp
    rw [Ideal.mem_bot.mp hp]
    simp
  let hX : (X j).eval₂ (algebraMap K Q) y = 1 := by
    simpa only [MvPolynomial.eval₂_X] using hyj
  let hzOne0 : (Ideal.Quotient.lift
      (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) K)).toIdeal
      (eval₂Hom (algebraMap K Q) y) he0)
        (Ideal.Quotient.mk
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) K)).toIdeal (X j)) = 1 := by
    exact hX
  obtain ⟨g0, hg0Point, hg0Coordinates⟩ :=
    exists_ambientCoordinateChart_of_quotientNormalizedPointAt
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
      y (X j) (isHomogeneous_X K j) he0 hzOne0 j
        (by rw [hyj]; exact one_ne_zero)
  have hbase0 : g0.comp (AllCharacteristics.GradedChart.baseMap
      (homogeneousSubmodule (Fin 4) K) (z := X j)) = algebraMap K Q := by
    apply RingHom.ext
    intro r
    have hs : Spec.map (CommRingCat.ofHom
        (g0.comp (AllCharacteristics.GradedChart.baseMap
          (homogeneousSubmodule (Fin 4) K) (z := X j)))) =
        Spec.map (CommRingCat.ofHom (algebraMap K Q)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      calc
        Spec.map (CommRingCat.ofHom g0) ≫
            Spec.map (CommRingCat.ofHom
              (AllCharacteristics.GradedChart.baseMap
                (homogeneousSubmodule (Fin 4) K) (z := X j))) =
          (Spec.map (CommRingCat.ofHom g0) ≫ chart) ≫ ambientToBase := by
            rw [Category.assoc,
              AllCharacteristics.HomogeneousProjective.ambientCoordinateChart_toBase]
        _ = (linearNormalizedPointAt
              (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
              y he0
              (Ideal.Quotient.mk
                (⊥ : HomogeneousIdeal
                  (homogeneousSubmodule (Fin 4) K)).toIdeal (X j))
              (polynomial_class_mem_grading
                (⊥ : HomogeneousIdeal
                  (homogeneousSubmodule (Fin 4) K))
                (X j) (isHomogeneous_X K j)) hzOne0 ≫
              quotientProjMap
                (⊥ : HomogeneousIdeal
                  (homogeneousSubmodule (Fin 4) K))) ≫ ambientToBase :=
          congrArg (fun k => k ≫ ambientToBase) hg0Point
        _ = Spec.map (CommRingCat.ofHom (algebraMap K Q)) := by
          rw [Category.assoc, quotientProjMap_toBase,
            linearNormalizedPointAt_toBase]
    exact RingHom.congr_fun
      (congrArg CommRingCat.Hom.hom (Spec.map_injective hs)) r
  have hg : g0 = gQ := by
    apply DFunLike.ext g0 gQ
    intro z
    obtain ⟨p, hp⟩ :=
      AllCharacteristics.HomogeneousProjective.ambientChartEvaluation_surjective
        (R := K) (σ := Fin 4) j z
    rw [← hp]
    change g0 (p.eval₂
        (AllCharacteristics.GradedChart.baseMap
          (homogeneousSubmodule (Fin 4) K) (z := X j))
        (AllCharacteristics.HomogeneousProjective.ambientChartCoordinate j)) =
      gQ (p.eval₂
        (AllCharacteristics.GradedChart.baseMap
          (homogeneousSubmodule (Fin 4) K) (z := X j))
        (AllCharacteristics.HomogeneousProjective.ambientChartCoordinate j))
    rw [MvPolynomial.hom_eval₂, MvPolynomial.hom_eval₂, hbase0, hbaseQ]
    congr 1
    funext k
    change g0 (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K j)
        (X k) (isHomogeneous_X K k)) = y k
    rw [hg0Coordinates k, hyj, inv_one, one_mul]
  refine ⟨y, hyj, ?_, he0, hX, ?_⟩
  · intro k
    exact RingHom.congr_fun hmaps _
  · rw [← linearNormalizedPointAt_mk_eq_linearNormalizedPoint
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
        y he0 (X j) (isHomogeneous_X K j) hzOne0,
      ← hg0Point, hg, hpQ]

/-- A normalized projective point which descends along a field embedding has
homogeneous coordinates over the smaller field whose images are obtained by
dividing by one nonzero coordinate. -/
theorem exists_coordinates_of_linearNormalizedPoint_factorization
    {K Q L : Type u} [Field K] [Field Q] [Field L]
    [Algebra K Q] [Algebra K L]
    (e : Q →ₐ[K] L)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → L)
    (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1)
    (hxell : ell.eval₂ (algebraMap K L) x = 1)
    (heq : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K L) x = 0)
    (q : Spec (.of Q) ⟶ scheme I)
    (hq : q ≫ toBase I =
      Spec.map (CommRingCat.ofHom (algebraMap K Q)))
    (hfactor : linearNormalizedPoint I x ell hell hxell heq =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q) :
    ∃ (j : Fin 4) (y : Fin 4 → Q),
      x j ≠ 0 ∧ y j = 1 ∧
      (∀ i : Fin 4, e (y i) = (x j)⁻¹ * x i) ∧
      ∃ (hey : ∀ p ∈ I.toIdeal,
          p.eval₂ (algebraMap K Q) y = 0)
        (hyX : (X j).eval₂ (algebraMap K Q) y = 1),
        linearNormalizedPoint I y (X j) (isHomogeneous_X K j) hyX hey = q := by
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simp at hxell
    have hzero : constantCoeff ell = 0 :=
      hell.coeff_eq_zero (by decide)
    exact zero_ne_one (hzero.symm.trans hxell)
  obtain ⟨j, hxj⟩ : ∃ j : Fin 4, x j ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  let ux : Lˣ := Units.mk0 (x j) hxj
  obtain ⟨gL, hgL, hpL⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint
      I x ell hell hxell heq j ux rfl
  have hj : q (IsLocalRing.closedPoint Q) ∈ Set.range (chartι I j) := by
    have hs : (Spec.map (CommRingCat.ofHom e.toRingHom))
        (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint Q :=
      Subsingleton.elim _ _
    refine ⟨(Spec.map (CommRingCat.ofHom gL))
      (IsLocalRing.closedPoint L), ?_⟩
    calc
      (chartι I j) ((Spec.map (CommRingCat.ofHom gL))
          (IsLocalRing.closedPoint L)) =
          (Spec.map (CommRingCat.ofHom gL) ≫ chartι I j)
            (IsLocalRing.closedPoint L) := rfl
      _ = (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q)
          (IsLocalRing.closedPoint L) := by
            exact congrArg
              (fun f : Spec (.of L) ⟶ scheme I =>
                f (IsLocalRing.closedPoint L))
              (hpL.trans hfactor)
      _ = q (IsLocalRing.closedPoint Q) := by
        exact congrArg q hs
  obtain ⟨gQ, hgQbase, hpQ⟩ :=
    exists_chart_hom_eq_of_point_of_mem_range I
      (algebraMap K Q) q hq j hj
  let y : Fin 4 → Q := fun i => gQ (chartCoordinate I j i)
  have hmaps : e.toRingHom.comp gQ = gL := by
    apply chart_hom_eq_of_projective_eq I
    calc
      Spec.map (CommRingCat.ofHom (e.toRingHom.comp gQ)) ≫ chartι I j =
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫
            (Spec.map (CommRingCat.ofHom gQ) ≫ chartι I j) := by
              rw [← Category.assoc, ← Spec.map_comp,
                ← CommRingCat.ofHom_comp]
      _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q := by rw [hpQ]
      _ = linearNormalizedPoint I x ell hell hxell heq := hfactor.symm
      _ = Spec.map (CommRingCat.ofHom gL) ≫ chartι I j := hpL.symm
  have hey : ∀ p ∈ I.toIdeal,
      p.eval₂ (algebraMap K Q) y = 0 := by
    intro p hp
    have h := congrArg gQ (eval₂_chartCoordinate_eq_zero_of_mem I j p hp)
    rw [MvPolynomial.hom_eval₂, hgQbase, map_zero] at h
    exact h
  have hyX : (X j).eval₂ (algebraMap K Q) y = 1 := by
    rw [MvPolynomial.eval₂_X]
    change gQ (chartCoordinate I j j) = 1
    rw [chartCoordinate_self, map_one]
  have hgQ : gQ =
      linearNormalizedPointChartMap I y (X j) hyX hey := by
    apply linearNormalizedPointChartMap_eq_of_base_and_coordinates
      I y (X j) (isHomogeneous_X K j) hyX hey gQ hgQbase
    intro k
    rfl
  have hpoint : linearNormalizedPoint I y (X j)
      (isHomogeneous_X K j) hyX hey = q := by
    change Spec.map (CommRingCat.ofHom
        (linearNormalizedPointChartMap I y (X j) hyX hey)) ≫
      chartι I j = q
    rw [← hgQ]
    exact hpQ
  refine ⟨j, y, hxj, ?_, ?_, hey, hyX, hpoint⟩
  · change gQ (chartCoordinate I j j) = 1
    rw [chartCoordinate_self, map_one]
  · intro i
    have hi := RingHom.congr_fun hmaps (chartCoordinate I j i)
    rw [hgL i] at hi
    simpa [y, ux] using hi

/-- Eight descended projective points inherit detection of the fixed
quadratic frame.  Each point may use a different standard coordinate chart;
homogeneity makes the resulting independent row scalings harmless. -/
theorem exists_descended_coordinates_detecting_quadraticEightFrame
    {K Q L : Type u} [Field K] [Field Q] [Field L]
    [Algebra K Q] [Algebra K L]
    (e : Q →ₐ[K] L)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 8 → Fin 4 → L)
    (ell : Fin 8 → MvPolynomial (Fin 4) K)
    (hell : ∀ i, (ell i).IsHomogeneous 1)
    (hxell : ∀ i, (ell i).eval₂ (algebraMap K L) (x i) = 1)
    (heq : ∀ i p, p ∈ I.toIdeal →
      p.eval₂ (algebraMap K L) (x i) = 0)
    (q : Fin 8 → (Spec (.of Q) ⟶ scheme I))
    (hq : ∀ i, q i ≫ toBase I =
      Spec.map (CommRingCat.ofHom (algebraMap K Q)))
    (hfactor : ∀ i,
      linearNormalizedPoint I (x i) (ell i) (hell i) (hxell i) (heq i) =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q i)
    (hdetect : ∀ c : Fin 8 → L,
      (∀ i, eval (x i)
        (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) →
      c = 0) :
    ∃ (j : Fin 8 → Fin 4) (y : Fin 8 → Fin 4 → Q),
      (∀ i, y i (j i) = 1) ∧
      (∀ i k, e (y i k) = (x i (j i))⁻¹ * x i k) ∧
      (∀ c : Fin 8 → Q,
        (∀ i, eval (y i)
          (homogeneousFrameMap 2 (quadraticEightFrame Q) c).1 = 0) →
        c = 0) ∧
      ∀ i, ∃ (hey : ∀ p ∈ I.toIdeal,
          p.eval₂ (algebraMap K Q) (y i) = 0)
        (hyX : (X (j i)).eval₂ (algebraMap K Q) (y i) = 1),
        linearNormalizedPoint I (y i) (X (j i))
          (isHomogeneous_X K (j i)) hyX hey = q i := by
  have hcoords : ∀ i : Fin 8, ∃ (j : Fin 4) (y : Fin 4 → Q),
      x i j ≠ 0 ∧ y j = 1 ∧
        (∀ k : Fin 4, e (y k) = (x i j)⁻¹ * x i k) ∧
        ∃ (hey : ∀ p ∈ I.toIdeal,
            p.eval₂ (algebraMap K Q) y = 0)
          (hyX : (X j).eval₂ (algebraMap K Q) y = 1),
          linearNormalizedPoint I y (X j)
            (isHomogeneous_X K j) hyX hey = q i := by
    intro i
    exact exists_coordinates_of_linearNormalizedPoint_factorization
      e I (x i) (ell i) (hell i) (hxell i) (heq i) (q i) (hq i)
        (hfactor i)
  choose j y hxj hyj hmap hey hyX hpoint using hcoords
  let s : Fin 8 → L := fun i => (x i (j i))⁻¹
  have hs : ∀ i, s i ≠ 0 := by
    intro i
    exact inv_ne_zero (hxj i)
  have hscaled := quadraticEightFrame_detection_rowScaling x s hs hdetect
  have himage : (fun i k => e (y i k)) = fun i => s i • x i := by
    funext i k
    exact hmap i k
  have himageDetect : ∀ c : Fin 8 → L,
      (∀ i, eval (fun k => e (y i k))
        (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) →
      c = 0 := by
    intro c hc
    apply hscaled c
    intro i
    rw [← congrFun himage i]
    exact hc i
  refine ⟨j, y, hyj, hmap, ?_, ?_⟩
  · exact quadraticEightFrame_detection_reflects e.toRingHom y himageDetect
  · intro i
    exact ⟨hey i, hyX i, hpoint i⟩

end PfaffianDescent

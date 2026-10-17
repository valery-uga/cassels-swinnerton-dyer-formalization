import PfaffianDescent.VoisinFixedCubicCoordinateFlat
import AllCharacteristics.ProjectiveEquationParameters
import PfaffianDescent.VoisinFieldPointEquationParameter
import PfaffianDescent.LocalSpecProjectiveEquationChart

/-!
# Regularity of the normalized equation at a field point

The equation pulled back from a projective coefficient chart is a nonzero
scalar multiple of the equation that classifies the field point. Thus
regularity modulo the fixed cubic is independent of the chosen coefficient
chart. This supplies the residue equation needed for local flatness.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A regular field-point cubic remains regular when expressed as the
normalized equation of any projective coefficient chart containing it. -/
theorem normalizedCubic_fieldPoint_regularModFixedCubic
    {K S : Type u} [Field K] [Field S]
    (b : K →+* S)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3)
    (j : Monomials (Fin 4) 3) (hj : p.coeff j.1 ≠ 0)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal (a.map b) (ha.map b)).toIdeal p)) :
    IsRegular (Ideal.Quotient.mk
      (equationIdeal (a.map b) (ha.map b)).toIdeal
      ((normalizedForm K (Fin 4) 3 j).map
        (projectiveEquationChartMap b p j hj))) := by
  rw [map_normalizedForm_equationChart b p j hj hp]
  let I := (equationIdeal (a.map b) (ha.map b)).toIdeal
  have hu : IsUnit (Ideal.Quotient.mk I (C (p.coeff j.1)⁻¹)) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hj)).map
      ((Ideal.Quotient.mk I).comp (C : S →+* MvPolynomial (Fin 4) S))
  have hm : Ideal.Quotient.mk I (C (p.coeff j.1)⁻¹ * p) =
      Ideal.Quotient.mk I (C (p.coeff j.1)⁻¹) *
        Ideal.Quotient.mk I p := map_mul _ _ _
  rw [hm]
  exact hu.isRegular.mul hreg

/-- A local pullback of a normalized coefficient chart has flat
intersection charts whenever its residue point represents a cubic regular
on the fixed surface. The equality of coefficient maps records that the
local parameter specializes to that actual field point. -/
theorem fixedCubic_normalizedIntersectionChart_flat_at_fieldPoint
    {K T : Type u} [Field K] [CommRing T] [Algebra K T]
    [IsLocalRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) (IsLocalRing.ResidueField T))
    (hp : p.IsHomogeneous 3)
    (j : Monomials (Fin 4) 3) (hj : p.coeff j.1 ≠ 0)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (hf : (algebraMap T (IsLocalRing.ResidueField T)).comp f =
      projectiveEquationChartMap
        (algebraMap K (IsLocalRing.ResidueField T)) p j hj)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal
        (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal p))
    (i : Fin 4) :
    let q := (normalizedForm K (Fin 4) 3 j).map f
    let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
    let J := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    ((chartQuotientMap J (J ⊔ equationIdeal q hq)
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) i).comp
      (chartBaseMap J i)).Flat := by
  let q := (normalizedForm K (Fin 4) 3 j).map f
  let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  have hreg' : IsRegular (Ideal.Quotient.mk
      (equationIdeal
        (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
      (q.map (algebraMap T (IsLocalRing.ResidueField T)))) := by
    simpa only [q, MvPolynomial.map_map, hf] using
      (normalizedCubic_fieldPoint_regularModFixedCubic
        (algebraMap K (IsLocalRing.ResidueField T))
        a ha p hp j hj hreg)
  exact fixedCubicIntersectionChart_flat_of_residue_regular
    a ha q hq hreg' i

/-- The normalized local equation has a regular principal kernel on every
fixed-surface chart, including over nonreduced local parameter rings. -/
theorem fixedCubic_normalizedIntersectionChart_regular_principalKernel_at_fieldPoint
    {K T : Type u} [Field K] [CommRing T] [Algebra K T]
    [IsLocalRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) (IsLocalRing.ResidueField T))
    (hp : p.IsHomogeneous 3)
    (j : Monomials (Fin 4) 3) (hj : p.coeff j.1 ≠ 0)
    (f : ParameterChartRing K (Fin 4) 3 j →+* T)
    (hf : (algebraMap T (IsLocalRing.ResidueField T)).comp f =
      projectiveEquationChartMap
        (algebraMap K (IsLocalRing.ResidueField T)) p j hj)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal
        (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal p))
    (i : Fin 4) :
    let q := (normalizedForm K (Fin 4) 3 j).map f
    let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
    let J := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    let x := q.eval₂ (chartBaseMap J i) (chartCoordinate J i)
    IsRegular x ∧
      RingHom.ker (chartQuotientMap J (J ⊔ equationIdeal q hq)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) i) =
        Ideal.span ({x} : Set (ChartRing J i)) := by
  let q := (normalizedForm K (Fin 4) 3 j).map f
  let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  have hreg' : IsRegular (Ideal.Quotient.mk
      (equationIdeal
        (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
      (q.map (algebraMap T (IsLocalRing.ResidueField T)))) := by
    simpa only [q, MvPolynomial.map_map, hf] using
      (normalizedCubic_fieldPoint_regularModFixedCubic
        (algebraMap K (IsLocalRing.ResidueField T))
        a ha p hp j hj hreg)
  exact fixedCubicIntersectionChart_regular_principalKernel_of_residue_regular
    a ha q hq hreg' i

/-- For every field point of Voisin's actual nontrivial equation family,
the cubic that classifies the parameter has a regular normalized equation
on its coefficient chart. This is the exact residue regularity used by the
local intersection-flatness theorem. -/
theorem flatGradedNontrivialOpen_fieldPoint_normalizedRegular
    {K R S : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R] [Field S] [Algebra R S]
    [Algebra K S] [IsScalarTower K R S]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase (a.map (algebraMap K S))
      (ha.map (algebraMap K S)))]
    (s : Spec (.of S) ⟶
      pullback (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hs : s ≫ pullback.snd
      (flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) = 𝟙 _) :
    ∃ (p : MvPolynomial (Fin 4) S) (_hp : p.IsHomogeneous 3)
      (j : Monomials (Fin 4) 3) (hj : p.coeff j.1 ≠ 0),
      IsRegular (Ideal.Quotient.mk
        (equationIdeal (a.map (algebraMap K S))
          (ha.map (algebraMap K S))).toIdeal
        ((normalizedForm K (Fin 4) 3 j).map
          (projectiveEquationChartMap (algebraMap K S) p j hj))) ∧
      s ≫ pullback.fst
        (flatGradedProjectiveFamilyNontrivialOpenToBase
          J r q e hRank a ha ha0)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫
          flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0 =
        projectiveEquationParameter (algebraMap K S) p j hj := by
  obtain ⟨p, hp, j, hj, _hpC, hreg, _hcharts, hparam⟩ :=
    flatGradedProjectiveFamilyNontrivialOpen_baseChange_fieldPoint_regularCharts_equationParameter
      J r q e hRank C hmap a ha ha0 s hs
  exact ⟨p, hp, j, hj,
    normalizedCubic_fieldPoint_regularModFixedCubic
      (algebraMap K S) a ha p hp j hj hreg,
    hparam⟩

/-- A local morphism to the projective space of moving cubics has flat
intersection charts with the fixed cubic whenever its residue parameter is
represented by a cubic regular on that surface. The normalized chart and
its coefficient homomorphism are produced from the local morphism itself. -/
theorem fixedCubic_localProjectiveIntersectionCharts_flat
    {K T : Type u} [Field K] [CommRing T] [IsLocalRing T]
    [Algebra K T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (v : Spec (.of T) ⟶ projectiveParameters K (Fin 4) 3)
    (p : MvPolynomial (Fin 4) (IsLocalRing.ResidueField T))
    (hp : p.IsHomogeneous 3)
    (j : Monomials (Fin 4) 3) (hj : p.coeff j.1 ≠ 0)
    (hpoint : Spec.map (CommRingCat.ofHom
        (algebraMap T (IsLocalRing.ResidueField T))) ≫ v =
      projectiveEquationParameter
        (algebraMap K (IsLocalRing.ResidueField T)) p j hj)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal
        (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal p)) :
    ∃ f : ParameterChartRing K (Fin 4) 3 j →+* T,
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j = v ∧
      ∀ i : Fin 4,
        let q := (normalizedForm K (Fin 4) 3 j).map f
        let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
        let J := equationIdeal (a.map (algebraMap K T))
          (ha.map (algebraMap K T))
        ((chartQuotientMap J (J ⊔ equationIdeal q hq)
          (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) i).comp
          (chartBaseMap J i)).Flat := by
  obtain ⟨f, hf, hres⟩ :=
    localSpec_projectiveEquationChartMap v p hp j hj hpoint
  refine ⟨f, hf, ?_⟩
  intro i
  exact fixedCubic_normalizedIntersectionChart_flat_at_fieldPoint
    a ha p hp j hj f hres hreg i

/-- A local equation parameter whose residue equation is regular supplies
regular principal kernels on all fixed-surface charts. -/
theorem fixedCubic_localProjectiveIntersectionCharts_regular_principalKernel
    {K T : Type u} [Field K] [CommRing T] [IsLocalRing T]
    [Algebra K T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (v : Spec (.of T) ⟶ projectiveParameters K (Fin 4) 3)
    (p : MvPolynomial (Fin 4) (IsLocalRing.ResidueField T))
    (hp : p.IsHomogeneous 3)
    (j : Monomials (Fin 4) 3) (hj : p.coeff j.1 ≠ 0)
    (hpoint : Spec.map (CommRingCat.ofHom
        (algebraMap T (IsLocalRing.ResidueField T))) ≫ v =
      projectiveEquationParameter
        (algebraMap K (IsLocalRing.ResidueField T)) p j hj)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal
        (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal p)) :
    ∃ f : ParameterChartRing K (Fin 4) 3 j →+* T,
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j = v ∧
      ∀ i : Fin 4,
        let q := (normalizedForm K (Fin 4) 3 j).map f
        let hq := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
        let J := equationIdeal (a.map (algebraMap K T))
          (ha.map (algebraMap K T))
        let x := q.eval₂ (chartBaseMap J i) (chartCoordinate J i)
        IsRegular x ∧
          RingHom.ker (chartQuotientMap J (J ⊔ equationIdeal q hq)
            (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) i) =
            Ideal.span ({x} : Set (ChartRing J i)) := by
  obtain ⟨f, hf, hres⟩ :=
    localSpec_projectiveEquationChartMap v p hp j hj hpoint
  refine ⟨f, hf, ?_⟩
  intro i
  exact fixedCubic_normalizedIntersectionChart_regular_principalKernel_at_fieldPoint
    a ha p hp j hj f hres hreg i

end PfaffianDescent

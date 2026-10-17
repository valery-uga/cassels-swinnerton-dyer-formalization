import PfaffianDescent.NormalizedProjectiveQuotientFactor
import AllCharacteristics.ProjectiveClassifyingMap

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_projectiveUniversalFamily_point_of_chart_evaluation_zero
    {R K L : Type u} [CommRing R] [Field K] [Field L]
    {σ : Type} [Finite σ]
    (a : R →+* K) (b : K →+* L)
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    (q : Spec (.of L) ⟶ scheme
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)))
    (j : σ) (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) j →+* L)
    (hgbase : g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) j) = b)
    (hgpoint : Spec.map (CommRingCat.ofHom g) ≫
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) j = q)
    (hzero : p.eval₂ b (fun i ↦ g (chartCoordinate
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) j i)) = 0) :
    ∃ u : Spec (.of L) ⟶ projectiveUniversalFamily R σ d,
      u ≫ projectiveUniversalIncidence R σ d =
        Limits.prod.lift
          (q ≫ quotientProjMap
            (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) ≫
              ambientCoefficientMap a)
          (Spec.map (CommRingCat.ofHom b) ≫
            projectiveClassifyingMap p hp hne a) := by
  obtain ⟨r, hrbase, _, hrambient⟩ :=
    exists_hypersurface_point_of_chart_evaluation_zero b p hp q j g hgbase hgpoint hzero
  let k := chosenEquationCoefficient p hp hne
  let hk : p.coeff k.1 ≠ 0 := chosenEquationCoefficient_ne_zero p hp hne
  let u : Spec (.of L) ⟶ projectiveUniversalFamily R σ d :=
    r ≫ projectiveEquationFiberToUniversalFamily a p k hk hp
  refine ⟨u, ?_⟩
  dsimp only [u]
  rw [Category.assoc,
    projectiveEquationFiberToUniversalFamily_comp_toIncidence]
  apply Limits.prod.hom_ext
  · rw [Category.assoc, Limits.prod.lift_fst, Limits.prod.lift_fst]
    change r ≫ quotientProjMap (equationIdeal p hp) ≫ ambientCoefficientMap a = _
    exact (Category.assoc r (quotientProjMap (equationIdeal p hp))
      (ambientCoefficientMap a)).symm.trans
      (congrArg (fun t ↦ t ≫ ambientCoefficientMap a) hrambient)
  · rw [Category.assoc, Limits.prod.lift_snd, Limits.prod.lift_snd]
    rw [← Category.assoc, hrbase]
    exact congrArg (fun t ↦ Spec.map (CommRingCat.ofHom b) ≫ t)
      (projectiveClassifyingMap_eq_chart p hp hne a k hk).symm

/-- A homogeneous equation vanishing on coordinates in an arbitrary
degree-one normalized chart supplies a point of the universal incidence
family.  This is the form used by normalized finite-subscheme charts, whose
normalizing linear form need not be a coordinate variable. -/
theorem exists_projectiveUniversalFamily_point_of_linearNormalized_evaluation_zero
    {R K L : Type u} [CommRing R] [Field K] [Field L]
    [Algebra K L] {σ : Type} [Finite σ]
    (a : R →+* K)
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    (x : σ → L)
    (heI : ∀ s ∈ (⊥ : HomogeneousIdeal
      (homogeneousSubmodule σ K)).toIdeal,
      (eval₂Hom (algebraMap K L) x) s = 0)
    (z : CoordinateRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)))
    (hz : z ∈ grading
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) 1)
    (hzOne : (Ideal.Quotient.lift
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)).toIdeal
      (eval₂Hom (algebraMap K L) x) heI) z = 1)
    (hzero : p.eval₂ (algebraMap K L) x = 0) :
    ∃ u : Spec (.of L) ⟶ projectiveUniversalFamily R σ d,
      u ≫ projectiveUniversalIncidence R σ d =
        Limits.prod.lift
          (linearNormalizedPointAt
              (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
              x heI z hz hzOne ≫
            quotientProjMap
              (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) ≫
            ambientCoefficientMap a)
          (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
            projectiveClassifyingMap p hp hne a) := by
  let I : HomogeneousIdeal (homogeneousSubmodule σ K) := ⊥
  let J : HomogeneousIdeal (homogeneousSubmodule σ K) := equationIdeal p hp
  let hIJ : I.toIdeal ≤ J.toIdeal := bot_le
  have heJ : ∀ s ∈ J.toIdeal,
      (eval₂Hom (algebraMap K L) x) s = 0 := by
    intro s hs
    apply (show J.toIdeal ≤ RingHom.ker
        (eval₂Hom (algebraMap K L) x) by
      apply Ideal.span_le.mpr
      intro q hq
      obtain rfl := Set.mem_singleton_iff.mp hq
      simpa using hzero) hs
  let zJ := gradedQuotientMap I J hIJ z
  have hzJ : zJ ∈ grading J 1 :=
    (gradedQuotientMap I J hIJ).map_mem hz
  have hzOneJ : (Ideal.Quotient.lift J.toIdeal
      (eval₂Hom (algebraMap K L) x) heJ) zJ = 1 := by
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective z
    have hqOne : (eval₂Hom (algebraMap K L) x) q = 1 := by
      rw [← hq] at hzOne
      rw [Ideal.Quotient.lift_mk] at hzOne
      exact hzOne
    dsimp only [zJ]
    rw [← hq]
    change Ideal.Quotient.lift J.toIdeal
      (eval₂Hom (algebraMap K L) x) heJ
        (Ideal.Quotient.mk J.toIdeal q) = 1
    rw [Ideal.Quotient.lift_mk]
    exact hqOne
  let r : Spec (.of L) ⟶ hypersurface p hp :=
    linearNormalizedPointAt J x heJ zJ hzJ hzOneJ
  have hfactor : r ≫ schemeQuotientMap I J hIJ =
      linearNormalizedPointAt I x heI z hz hzOne := by
    exact linearNormalizedPointAt_comp_schemeQuotientMap
      I J hIJ x heI heJ z hz hzOne hzOneJ
  have hrambient : r ≫ hypersurfaceToAmbient p hp =
      linearNormalizedPointAt
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
          x heI z hz hzOne ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) := by
    change r ≫ quotientProjMap (equationIdeal p hp) = _
    have hcomp := schemeQuotientMap_comp_quotientProjMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
      (equationIdeal p hp) bot_le
    have hfactor' : r ≫ schemeQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
        (equationIdeal p hp) bot_le =
      linearNormalizedPointAt
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
          x heI z hz hzOne := by
      simpa only [I, J, hIJ] using hfactor
    rw [← hcomp]
    exact (Category.assoc r
      (schemeQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
        (equationIdeal p hp) bot_le)
      (quotientProjMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)))).symm.trans
      (congrArg (fun t ↦ t ≫ quotientProjMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))) hfactor')
  have hrbase : r ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    dsimp only [r]
    exact linearNormalizedPointAt_toBase J x heJ zJ hzJ hzOneJ
  let k := chosenEquationCoefficient p hp hne
  let hk : p.coeff k.1 ≠ 0 := chosenEquationCoefficient_ne_zero p hp hne
  let u : Spec (.of L) ⟶ projectiveUniversalFamily R σ d :=
    r ≫ projectiveEquationFiberToUniversalFamily a p k hk hp
  refine ⟨u, ?_⟩
  dsimp only [u]
  rw [Category.assoc,
    projectiveEquationFiberToUniversalFamily_comp_toIncidence]
  apply Limits.prod.hom_ext
  · rw [Category.assoc, Limits.prod.lift_fst, Limits.prod.lift_fst]
    rw [← Category.assoc, hrambient]
    exact Category.assoc _ _ _
  · rw [Category.assoc, Limits.prod.lift_snd, Limits.prod.lift_snd]
    rw [← Category.assoc, hrbase]
    exact congrArg
      (fun t ↦ Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ t)
      (projectiveClassifyingMap_eq_chart p hp hne a k hk).symm

end PfaffianDescent

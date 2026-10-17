import PfaffianDescent.HomogeneousQuotientMap
import PfaffianDescent.LinearNormalizedProjectivePoint

/-!
# Normalized projective points through homogeneous quotients

A finite projective point reconstructed in a chosen linear chart is compatible
with passage to a larger homogeneous ideal.  This preserves its chart map while
imposing extra homogeneous equations.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

section

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective-spectrum form of a normalized point.  It is kept with
codomain `Proj` rather than the opaque projective-scheme wrapper so quotient
compatibility can be proved by the affine-chart formula itself. -/
noncomputable def normalizedProjectivePointAt
    (I : HomogeneousIdeal (homogeneousSubmodule σ K)) (x : σ → A)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0)
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) x) he) z = 1) :
    Spec (.of A) ⟶ Proj (grading I) :=
  Spec.map (CommRingCat.ofHom (linearNormalizedPointChartMapAt I x he z hz hzOne)) ≫
    Proj.awayι (grading I) z hz (by decide : 0 < 1)

variable (I J : HomogeneousIdeal (homogeneousSubmodule σ K))
  (hIJ : I.toIdeal ≤ J.toIdeal)
  (x : σ → A)
  (heI : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0)
  (heJ : ∀ p ∈ J.toIdeal, p.eval₂ (algebraMap K A) x = 0)
  (z : CoordinateRing I) (hz : z ∈ grading I 1)
  (hzOneI : (Ideal.Quotient.lift I.toIdeal
    (eval₂Hom (algebraMap K A) x) heI) z = 1)
  (hzOneJ : (Ideal.Quotient.lift J.toIdeal
    (eval₂Hom (algebraMap K A) x) heJ)
      (gradedQuotientMap I J hIJ z) = 1)

/-- Reconstructing a normalized point after adding homogeneous equations and
then forgetting those equations gives the original reconstructed point. -/
theorem normalizedProjectivePointAt_comp_gradedQuotientMap :
    normalizedProjectivePointAt J x heJ (gradedQuotientMap I J hIJ z)
        ((gradedQuotientMap I J hIJ).map_mem hz) hzOneJ ≫
      Proj.map (gradedQuotientMap I J hIJ)
        (gradedSurjective_irrelevant_le (gradedQuotientMap I J hIJ)
          (gradedQuotientMap_surjective I J hIJ)) =
    normalizedProjectivePointAt I x heI z hz hzOneI := by
  let gI := linearNormalizedPointChartMapAt I x heI z hz hzOneI
  let gJ := linearNormalizedPointChartMapAt J x heJ
    (gradedQuotientMap I J hIJ z) ((gradedQuotientMap I J hIJ).map_mem hz) hzOneJ
  have hg : gJ.comp (awayQuotientMap I J hIJ z hz) = gI := by
    apply linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
      I x heI z hz hzOneI (gJ.comp (awayQuotientMap I J hIJ z hz))
    · apply RingHom.ext
      intro r
      change gJ (awayQuotientMap I J hIJ z hz
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z) r)) =
          algebraMap K A r
      rw [awayQuotientMap_baseMap]
      exact linearNormalizedPointChartMapAt_base J x heJ
        (gradedQuotientMap I J hIJ z) ((gradedQuotientMap I J hIJ).map_mem hz) hzOneJ r
    · intro j
      change gJ (awayQuotientMap I J hIJ z hz
        (linearChartCoordinate I z hz j)) = x j
      rw [awayQuotientMap_linearChartCoordinate]
      exact linearNormalizedPointChartMapAt_coordinate J x heJ
        (gradedQuotientMap I J hIJ z) ((gradedQuotientMap I J hIJ).map_mem hz) hzOneJ j
  change (Spec.map (CommRingCat.ofHom gJ) ≫
      Proj.awayι (grading J) (gradedQuotientMap I J hIJ z)
        ((gradedQuotientMap I J hIJ).map_mem hz) (by decide : 0 < 1)) ≫
      Proj.map (gradedQuotientMap I J hIJ)
        (gradedSurjective_irrelevant_le (gradedQuotientMap I J hIJ)
          (gradedQuotientMap_surjective I J hIJ)) =
    Spec.map (CommRingCat.ofHom gI) ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1)
  rw [Category.assoc]
  rw [AllCharacteristics.awayι_comp_map_of_eq
    (gradedQuotientMap I J hIJ)
    (gradedSurjective_irrelevant_le (gradedQuotientMap I J hIJ)
      (gradedQuotientMap_surjective I J hIJ))
    z (gradedQuotientMap I J hIJ z) rfl (by decide : 0 < 1) hz
    ((gradedQuotientMap I J hIJ).map_mem hz)]
  rw [← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (awayQuotientMap I J hIJ z hz) ≫
      CommRingCat.ofHom gJ) ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1) =
    Spec.map (CommRingCat.ofHom gI) ≫
      Proj.awayι (grading I) z hz (by decide : 0 < 1)
  have hcomp : CommRingCat.ofHom (awayQuotientMap I J hIJ z hz) ≫
      CommRingCat.ofHom gJ =
    CommRingCat.ofHom (gJ.comp (awayQuotientMap I J hIJ z hz)) := rfl
  rw [hcomp, hg]

/-- The quotient compatibility expressed through the projective-scheme
wrapper used by the complete-intersection construction. -/
theorem linearNormalizedPointAt_comp_schemeQuotientMap :
    linearNormalizedPointAt J x heJ (gradedQuotientMap I J hIJ z)
        ((gradedQuotientMap I J hIJ).map_mem hz) hzOneJ ≫
      schemeQuotientMap I J hIJ =
    linearNormalizedPointAt I x heI z hz hzOneI := by
  change normalizedProjectivePointAt J x heJ (gradedQuotientMap I J hIJ z)
      ((gradedQuotientMap I J hIJ).map_mem hz) hzOneJ ≫
    Proj.map (gradedQuotientMap I J hIJ)
      (gradedSurjective_irrelevant_le (gradedQuotientMap I J hIJ)
        (gradedQuotientMap_surjective I J hIJ)) =
    normalizedProjectivePointAt I x heI z hz hzOneI
  exact normalizedProjectivePointAt_comp_gradedQuotientMap I J hIJ x heI heJ z hz
    hzOneI hzOneJ

/-- The normalized point obtained after imposing additional homogeneous
equations is a closed immersion whenever the original homogeneous coordinates
generate the finite coefficient algebra. -/
theorem linearNormalizedPointAt_quotientEmbedding [Module.Finite K A]
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x)) :
    IsClosedImmersion
      (linearNormalizedPointAt J x heJ (gradedQuotientMap I J hIJ z)
        ((gradedQuotientMap I J hIJ).map_mem hz) hzOneJ) ∧
    linearNormalizedPointAt J x heJ (gradedQuotientMap I J hIJ z)
        ((gradedQuotientMap I J hIJ).map_mem hz) hzOneJ ≫
      schemeQuotientMap I J hIJ =
    linearNormalizedPointAt I x heI z hz hzOneI := by
  refine ⟨linearNormalizedPointAt_isClosedImmersion J x heJ
    (gradedQuotientMap I J hIJ z) ((gradedQuotientMap I J hIJ).map_mem hz)
    hzOneJ hgen, ?_⟩
  exact linearNormalizedPointAt_comp_schemeQuotientMap I J hIJ x heI heJ z hz
    hzOneI hzOneJ

/-- If a field-valued projective point is presented in one coordinate chart
and a homogeneous equation vanishes on its normalized chart coordinates,
then the point factors through the corresponding hypersurface.  The
factorization retains both the coefficient-field morphism and the exact
projective point, rather than only its carrier point. -/
theorem exists_hypersurface_point_of_chart_evaluation_zero
    {L : Type u} [Field L]
    (b : K →+* L) (p : MvPolynomial σ K) {d : ℕ}
    (hp : p.IsHomogeneous d)
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
    ∃ r : Spec (.of L) ⟶ hypersurface p hp,
      r ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom b) ∧
      r ≫ schemeQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
        (equationIdeal p hp) bot_le = q ∧
      r ≫ quotientProjMap (equationIdeal p hp) =
        q ≫ quotientProjMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) := by
  letI : Algebra K L := b.toAlgebra
  let I : HomogeneousIdeal (homogeneousSubmodule σ K) := ⊥
  let J : HomogeneousIdeal (homogeneousSubmodule σ K) := equationIdeal p hp
  let hIJ : I.toIdeal ≤ J.toIdeal := bot_le
  let x : σ → L := fun i ↦ g (chartCoordinate I j i)
  have heI : ∀ s ∈ I.toIdeal,
      (eval₂Hom (algebraMap K L) x) s = 0 := by
    intro s hs
    have : s = 0 := by simpa [I] using hs
    subst s
    simp
  have heJ : ∀ s ∈ J.toIdeal,
      (eval₂Hom (algebraMap K L) x) s = 0 := by
    intro s hs
    apply (show J.toIdeal ≤ RingHom.ker (eval₂Hom (algebraMap K L) x) by
      apply Ideal.span_le.mpr
      intro a ha
      have ha' : a = p := Set.mem_singleton_iff.mp ha
      subst a
      have hb : algebraMap K L = b := rfl
      rw [hb]
      change eval₂Hom b (fun i ↦ g (chartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) j i)) p = 0
      exact hzero) hs
  let z : CoordinateRing I := coordinate I j
  have hz : z ∈ grading I 1 := coordinate_mem I j
  have hzOneI : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K L) x) heI) z = 1 := by
    rw [show z = Ideal.Quotient.mk I.toIdeal (MvPolynomial.X j) by rfl,
      Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']
    dsimp only [x]
    rw [chartCoordinate_self, map_one]
  let zJ := gradedQuotientMap I J hIJ z
  have hzJ : zJ ∈ grading J 1 := (gradedQuotientMap I J hIJ).map_mem hz
  have hzOneJ : (Ideal.Quotient.lift J.toIdeal
      (eval₂Hom (algebraMap K L) x) heJ) zJ = 1 := by
    rw [show zJ = Ideal.Quotient.mk J.toIdeal (MvPolynomial.X j) by rfl,
      Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']
    dsimp only [x]
    rw [chartCoordinate_self, map_one]
  let r : Spec (.of L) ⟶ hypersurface p hp :=
    linearNormalizedPointAt J x heJ zJ hzJ hzOneJ
  have hfactor : r ≫ schemeQuotientMap I J hIJ = q := by
    have hr : r ≫ schemeQuotientMap I J hIJ =
        linearNormalizedPointAt I x heI z hz hzOneI := by
      dsimp only [r]
      exact linearNormalizedPointAt_comp_schemeQuotientMap I J hIJ x heI heJ z hz
        hzOneI hzOneJ
    rw [hr]
    change Spec.map (CommRingCat.ofHom
      (linearNormalizedPointChartMapAt I x heI z hz hzOneI)) ≫
        chartι I j = q
    rw [← hgpoint]
    have hmaps : linearNormalizedPointChartMapAt I x heI z hz hzOneI = g := by
      symm
      apply linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
        I x heI z hz hzOneI g
      · exact hgbase
      · intro i
        rfl
    rw [hmaps]
  refine ⟨r, linearNormalizedPointAt_toBase J x heJ zJ hzJ hzOneJ,
    hfactor, ?_⟩
  change r ≫ quotientProjMap (equationIdeal p hp) =
    q ≫ quotientProjMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
  have hcomp := schemeQuotientMap_comp_quotientProjMap
    (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
    (equationIdeal p hp) bot_le
  have hfactor' : r ≫ schemeQuotientMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))
      (equationIdeal p hp) bot_le = q := by
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

end

end PfaffianDescent
